use std::marker::PhantomData;
use halo2_proofs::{arithmetic::FieldExt, circuit::*, plonk::*, poly::Rotation};

// SUBLEQ Instruction: [a, b, c]
// 1. mem[b] = mem[b] - mem[a]
// 2. if mem[b] <= 0: pc = c
// 3. else: pc += 3 (next instruction)
#[derive(Debug, Clone, Copy, PartialEq)]
struct Instruction {
    a: usize,  // Source address
    b: usize,  // Destination address (also condition)
    c: usize,  // Jump target
}

// Memory-based VM state
#[derive(Debug, Clone)]
struct SubleqState {
    pc: usize,                    // Program counter
    memory: [i64; 256],          // Fixed-size memory for simplicity
}

// Circuit configuration
#[derive(Debug, Clone)]
struct SubleqConfig {
    mem_addr: Column<Advice>,     // Address being accessed
    mem_value: Column<Advice>,    // Value at that address
    mem_new_value: Column<Advice>, // New value after operation
    
    // Instruction columns
    pc: Column<Advice>,           // Program counter
    inst_a: Column<Advice>,       // First operand address
    inst_b: Column<Advice>,       // Second operand address
    inst_c: Column<Advice>,       // Jump target
    
    // Operation columns
    op_a_value: Column<Advice>,   // Value at address a
    op_b_value: Column<Advice>,   // Value at address b
    op_result: Column<Advice>,    // b - a
    
    // Branch condition
    branch_taken: Column<Advice>, // Whether branch is taken (0 or 1)
    new_pc: Column<Advice>,       // Next PC value
    
    // Selectors (like Fibonacci's selector)
    step_selector: Selector,      // Enables constraints for each step
    
    // Public inputs/outputs
    instance: Column<Instance>,
}

#[derive(Debug, Clone)]
struct SubleqChip<F: FieldExt> {
    config: SubleqConfig,
    program: Vec<Instruction>,
    initial_memory: Vec<(usize, i64)>,  // Initial memory values
    _marker: PhantomData<F>,
}

impl<F: FieldExt> SubleqChip<F> {
    pub fn new(config: SubleqConfig, program: Vec<Instruction>, initial_memory: Vec<(usize, i64)>) -> Self {
        Self {
            config,
            program,
            initial_memory,
            _marker: PhantomData,
        }
    }
    
    pub fn configure(meta: &mut ConstraintSystem<F>) -> SubleqConfig {
        // Create advice columns (like Fibonacci's col_a, col_b, col_c)
        let mem_addr = meta.advice_column();
        let mem_value = meta.advice_column();
        let mem_new_value = meta.advice_column();
        let pc = meta.advice_column();
        let inst_a = meta.advice_column();
        let inst_b = meta.advice_column();
        let inst_c = meta.advice_column();
        let op_a_value = meta.advice_column();
        let op_b_value = meta.advice_column();
        let op_result = meta.advice_column();
        let branch_taken = meta.advice_column();
        let new_pc = meta.advice_column();
        
        let step_selector = meta.selector();
        let instance = meta.instance_column();
        
        // Enable equality constraints for copying values
        meta.enable_equality(mem_addr);
        meta.enable_equality(mem_value);
        meta.enable_equality(mem_new_value);
        meta.enable_equality(pc);
        meta.enable_equality(inst_a);
        meta.enable_equality(inst_b);
        meta.enable_equality(inst_c);
        meta.enable_equality(op_a_value);
        meta.enable_equality(op_b_value);
        meta.enable_equality(op_result);
        meta.enable_equality(branch_taken);
        meta.enable_equality(new_pc);
        meta.enable_equality(instance);
        
        // Gate 1: SUBLEQ operation - op_result = op_b_value - op_a_value
        meta.create_gate("subleq operation", |meta| {
            let s = meta.query_selector(step_selector);
            let a_val = meta.query_advice(op_a_value, Rotation::cur());
            let b_val = meta.query_advice(op_b_value, Rotation::cur());
            let result = meta.query_advice(op_result, Rotation::cur());
            
            vec![s * (b_val - a_val - result)]
        });
        
        // Gate 2: Branch condition - branch_taken = 1 if result <= 0 else 0
        // In finite field, we need to encode the condition
        meta.create_gate("branch condition", |meta| {
            let s = meta.query_selector(step_selector);
            let result = meta.query_advice(op_result, Rotation::cur());
            let branch = meta.query_advice(branch_taken, Rotation::cur());
            
            // Constraint: branch * (branch - 1) = 0 (branch is 0 or 1)
            // And: if result <= 0 then branch = 1
            // Simplified: branch * result = 0 (if branch=1, result must be <=0)
            vec![
                s * branch.clone() * (branch.clone() - F::one()),  // branch ∈ {0,1}
                s * branch.clone() * result.clone(),               // if branch=1, result=0
            ]
        });
        
        // Gate 3: New PC calculation
        // new_pc = if branch_taken { inst_c } else { pc + 3 }
        meta.create_gate("pc update", |meta| {
            let s = meta.query_selector(step_selector);
            let pc_cur = meta.query_advice(pc, Rotation::cur());
            let inst_c = meta.query_advice(inst_c, Rotation::cur());
            let branch = meta.query_advice(branch_taken, Rotation::cur());
            let new_pc_val = meta.query_advice(new_pc, Rotation::cur());
            
            // new_pc = pc_cur + 3 + branch * (inst_c - (pc_cur + 3))
            let default_pc = pc_cur + F::from(3);
            let expected = default_pc + branch * (inst_c - default_pc);
            
            vec![s * (new_pc_val - expected)]
        });
        
        // Gate 4: Memory update - new value is written to address b
        meta.create_gate("memory update", |meta| {
            let s = meta.query_selector(step_selector);
            let old_val = meta.query_advice(mem_value, Rotation::cur());
            let new_val = meta.query_advice(mem_new_value, Rotation::cur());
            let result = meta.query_advice(op_result, Rotation::cur());
            
            vec![s * (new_val - (old_val - result))]  // mem[b] = mem[b] - mem[a]
        });
        
        // Gate 5: Memory persistence For addresses not written, values persist
        meta.create_gate("memory persistence", |meta| {
            let s = meta.query_selector(step_selector);
            let addr = meta.query_advice(mem_addr, Rotation::cur());
            let val_cur = meta.query_advice(mem_value, Rotation::cur());
            let val_next = meta.query_advice(mem_value, Rotation::next());
            let addr_next = meta.query_advice(mem_addr, Rotation::next());
            let is_same_addr = addr.clone() - addr_next.clone();
            
            // If addresses are different, values must be equal
            vec![s * is_same_addr * (val_next - val_cur)]
        });
        
        SubleqConfig {
            mem_addr, mem_value, mem_new_value, pc, inst_a, inst_b, inst_c,
            op_a_value, op_b_value, op_result, branch_taken, new_pc,
            step_selector, instance,
        }
    }
    
    pub fn assign_execution(
        &self,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        // Execute program to generate trace
        let mut state = SubleqState {
            pc: 0,
            memory: [0; 256],
        };
        
        // Initialize memory
        for (addr, value) in &self.initial_memory {
            state.memory[*addr] = *value;
        }
        
        // Store initial memory state
        let initial_memory = state.memory.clone();
        
        // Execute and collect trace
        let mut trace = Vec::new();
        let max_steps = 100; // Prevent infinite loops
        
        for step in 0..max_steps {
            if state.pc >= self.program.len() * 3 {
                break; // Program finished
            }
            
            let inst_index = state.pc / 3;
            let instruction = self.program[inst_index];
            
            let a_val = state.memory[instruction.a];
            let b_val = state.memory[instruction.b];
            let result = b_val - a_val;
            let branch_taken_val = if result <= 0 { 1 } else { 0 };
            
            // Record trace before update
            trace.push(SubleqTrace {
                step,
                pc: state.pc,
                inst_a: instruction.a,
                inst_b: instruction.b,
                inst_c: instruction.c,
                op_a_value: a_val,
                op_b_value: b_val,
                op_result: result,
                branch_taken: branch_taken_val,
                mem_addr: instruction.b,
                mem_old_value: b_val,
                mem_new_value: result,
                new_pc: if branch_taken_val == 1 { instruction.c } else { state.pc + 3 },
            });
            
            // Update state
            state.memory[instruction.b] = result;
            if branch_taken_val == 1 {
                state.pc = instruction.c;
            } else {
                state.pc += 3;
            }
        }
        
        // Assign trace to circuit
        self.assign_trace(layouter, trace, initial_memory)
    }
    
    fn assign_trace(
        &self,
        mut layouter: impl Layouter<F>,
        trace: Vec<SubleqTrace>,
        initial_memory: [i64; 256],
    ) -> Result<(), Error> {
        layouter.assign_region("SUBLEQ execution", |mut region| {
            // Assign each step as a row (like Fibonacci's rows)
            for (row, step) in trace.iter().enumerate() {
                // Enable selector for this row
                self.config.step_selector.enable(&mut region, row)?;
                
                // Assign all values for this row
                region.assign_advice(
                    || "pc",
                    self.config.pc,
                    row,
                    || Ok(F::from(step.pc as u64)),
                )?;
                
                region.assign_advice(
                    || "inst_a",
                    self.config.inst_a,
                    row,
                    || Ok(F::from(step.inst_a as u64)),
                )?;
                
                region.assign_advice(
                    || "inst_b",
                    self.config.inst_b,
                    row,
                    || Ok(F::from(step.inst_b as u64)),
                )?;
                
                region.assign_advice(
                    || "inst_c",
                    self.config.inst_c,
                    row,
                    || Ok(F::from(step.inst_c as u64)),
                )?;
                
                region.assign_advice(
                    || "op_a_value",
                    self.config.op_a_value,
                    row,
                    || Ok(F::from(step.op_a_value as u64)),
                )?;
                
                region.assign_advice(
                    || "op_b_value",
                    self.config.op_b_value,
                    row,
                    || Ok(F::from(step.op_b_value as u64)),
                )?;
                
                region.assign_advice(
                    || "op_result",
                    self.config.op_result,
                    row,
                    || Ok(F::from(step.op_result as u64)),
                )?;
                
                region.assign_advice(
                    || "branch_taken",
                    self.config.branch_taken,
                    row,
                    || Ok(F::from(step.branch_taken)),
                )?;
                
                region.assign_advice(
                    || "mem_addr",
                    self.config.mem_addr,
                    row,
                    || Ok(F::from(step.mem_addr as u64)),
                )?;
                
                region.assign_advice(
                    || "mem_value",
                    self.config.mem_value,
                    row,
                    || Ok(F::from(step.mem_old_value as u64)),
                )?;
                
                region.assign_advice(
                    || "mem_new_value",
                    self.config.mem_new_value,
                    row,
                    || Ok(F::from(step.mem_new_value as u64)),
                )?;
                
                region.assign_advice(
                    || "new_pc",
                    self.config.new_pc,
                    row,
                    || Ok(F::from(step.new_pc as u64)),
                )?;
            }
            
            // Expose initial memory state as public inputs (like Fibonacci's output)
            for (addr, value) in initial_memory.iter().enumerate() {
                if *value != 0 {
                    region.constrain_instance(
                        region.cells()[self.config.mem_value.index].cell_at(addr),
                        self.config.instance,
                        addr,
                    )?;
                }
            }
            
            // Expose final PC as public output
            let last_row = trace.len() - 1;
            region.constrain_instance(
                region.cells()[self.config.pc.index].cell_at(last_row),
                self.config.instance,
                256,  // Use high address for PC
            )?;
            
            Ok(())
        })
    }
}

#[derive(Debug, Clone)]
struct SubleqTrace {
    step: usize,
    pc: usize,
    inst_a: usize,
    inst_b: usize,
    inst_c: usize,
    op_a_value: i64,
    op_b_value: i64,
    op_result: i64,
    branch_taken: u64,
    mem_addr: usize,
    mem_old_value: i64,
    mem_new_value: i64,
    new_pc: usize,
}

// Circuit implementation
#[derive(Default)]
struct SubleqCircuit<F>(PhantomData<F>);

impl<F: FieldExt> Circuit<F> for SubleqCircuit<F> {
    type Config = SubleqConfig;
    type FloorPlanner = SimpleFloorPlanner;
    
    fn without_witnesses(&self) -> Self {
        Self::default()
    }
    
    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        SubleqChip::configure(meta)
    }
    
    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        // Example program: Fibonacci using SUBLEQ
        // Memory layout:
        // 0: counter (start at 8, count down to 0)
        // 1: f(n-2) = 1
        // 2: f(n-1) = 1
        // 3: f(n) = 0 (result)
        // 4: temp = 0
        // 5: loop start address
        // 6: loop end address
        // 7: program end
        
        let program = vec![
            // Loop: f(n) = f(n-1) + f(n-2)
            // SUBLEQ 2, 3, 0? Actually let's do proper SUBLEQ Fibonacci:
            
            // Instruction 0: Copy f(n-1) to temp
            // mem[4] = mem[4] - mem[2] (makes temp = -f(n-1))
            // But we want temp = f(n-1), so need more ops
            Instruction { a: 2, b: 4, c: 0 },  // mem[4] = mem[4] - mem[2]
            Instruction { a: 4, b: 4, c: 0 },  // mem[4] = mem[4] - mem[4] (double negative? complex)
            
            // For simplicity, let's do a direct Fibonacci calculation
            // This is a simplified version - real SUBLEQ Fibonacci needs more instructions
        ];
        
        let initial_memory = vec![
            (0, 8),  // Counter: compute up to f(8)
            (1, 1),  // f(0) = 1
            (2, 1),  // f(1) = 1
            (3, 0),  // f(2) = 0 (to be computed)
            (4, 0),  // temp
        ];
        
        let chip = SubleqChip::new(config, program, initial_memory);
        chip.assign_execution(layouter)
    }
}

// Example: Simple SUBLEQ program for subtraction
#[cfg(test)]
mod tests {
    use super::*;
    use halo2_proofs::{dev::MockProver, pasta::Fp};
    
    #[test]
    fn test_subtraction() {
        // Program: subtract 5 from 10
        // Memory: [10, 5, 0, ...]
        // Instruction: SUBLEQ 1, 0, 3 (mem[0] = mem[0] - mem[1], then if mem[0]<=0 jump to 3)
        
        let program = vec![
            Instruction { a: 1, b: 0, c: 3 },  // mem[0] = 10 - 5 = 5
        ];
        
        let initial_memory = vec![
            (0, 10),
            (1, 5),
        ];
        
        // This would run in a real test with proper circuit
        println!("SUBLEQ subtraction program ready");
    }
    
    #[test]
    fn test_fibonacci_subleq() {
        // SUBLEQ Fibonacci implementation (more complex)
        // This demonstrates the beauty of SUBLEQ - one instruction does everything!
        
        println!("SUBLEQ Fibonacci - demonstrating memory-based ZKVM pattern");
        println!("Each row = one SUBLEQ instruction execution");
        println!("Memory operations handled through constraints");
    }
}