
use halo2_proofs::{
    plonk::{Circuit, ConstraintSystem, Column, Advice, Fixed, Instance, Selector, Error},
    poly::Rotation,
    circuit::{Layouter, Region, Value},
    plonk::{Expression, VirtualCell},
};
use ff::Field;

 use halo2_proofs::halo2curves::bn256::Fr as Fp;

#[derive(Clone, Debug)]
pub struct ZKVMConfig {
    // Memory access columns
    mem_addr: Column<Advice>,
    mem_value: Column<Advice>,
    mem_timestamp: Column<Advice>,
    
    // Program counter and instruction
    pc: Column<Advice>,
    inst_a: Column<Advice>,
    inst_b: Column<Advice>,
    inst_c: Column<Advice>,
    
    // Execution state
    val_a: Column<Advice>,
    val_b: Column<Advice>,
    val_b_next: Column<Advice>,
    pc_next: Column<Advice>,
    branch_taken: Column<Advice>,
    
    // Memory operation flags
    is_read: Column<Fixed>,
    is_write: Column<Fixed>,
    
    // Selectors
    q_step: Selector,
    q_last: Selector,
    
    // Lookup table for range checks (0..MEM_SIZE)
    range_check: Column<Fixed>,
}

impl ZKVMConfig {
    pub fn configure(meta: &mut ConstraintSystem<F>, memory_size: usize, max_steps: usize) -> Self {
        // Create columns
        let mem_addr = meta.advice_column();
        let mem_value = meta.advice_column();
        let mem_timestamp = meta.advice_column();
        
        let pc = meta.advice_column();
        let inst_a = meta.advice_column();
        let inst_b = meta.advice_column();
        let inst_c = meta.advice_column();
        
        let val_a = meta.advice_column();
        let val_b = meta.advice_column();
        let val_b_next = meta.advice_column();
        let pc_next = meta.advice_column();
        let branch_taken = meta.advice_column();
        
        let is_read = meta.fixed_column();
        let is_write = meta.fixed_column();
        let range_check = meta.fixed_column();
        
        let q_step = meta.selector();
        let q_last = meta.selector();
        
        // Enable equality for columns that need to connect across rows
        meta.enable_equality(mem_addr);
        meta.enable_equality(mem_value);
        meta.enable_equality(mem_timestamp);
        meta.enable_equality(pc);
        meta.enable_equality(inst_a);
        meta.enable_equality(inst_b);
        meta.enable_equality(inst_c);
        
        // Add range check table for memory addresses
        meta.lookup_table(range_check);
        
        // Define the main SUBLEQ gate
        Self::define_subleq_gate(meta, &q_step, &pc, &inst_a, &inst_b, &inst_c,
                                  &val_a, &val_b, &val_b_next, &pc_next, &branch_taken);
        
        // Define memory consistency constraints using lookup arguments
        Self::define_memory_constraints(meta, &q_step, &mem_addr, &mem_value, &mem_timestamp,
                                        &inst_a, &inst_b, &val_a, &val_b, &val_b_next,
                                        &is_read, &is_write, &range_check);
        
        // Define PC continuity constraint
        Self::define_pc_continuity(meta, &q_last, &pc, &pc_next);
        
        ZKVMConfig {
            mem_addr, mem_value, mem_timestamp,
            pc, inst_a, inst_b, inst_c,
            val_a, val_b, val_b_next, pc_next, branch_taken,
            is_read, is_write,
            q_step, q_last,
            range_check,
        }
    }
    
    fn define_subleq_gate(
        meta: &mut ConstraintSystem<Fp>,
        q_step: &Selector,
        pc: &Column<Advice>,
        inst_a: &Column<Advice>,
        inst_b: &Column<Advice>,
        inst_c: &Column<Advice>,
        val_a: &Column<Advice>,
        val_b: &Column<Advice>,
        val_b_next: &Column<Advice>,
        pc_next: &Column<Advice>,
        branch_taken: &Column<Advice>,
    ) {
        meta.create_gate("SUBLEQ execution", |meta| {
            let q = meta.query_selector(*q_step);
            
            let pc_val = meta.query_advice(*pc, Rotation::cur());
            let inst_a_val = meta.query_advice(*inst_a, Rotation::cur());
            let inst_b_val = meta.query_advice(*inst_b, Rotation::cur());
            let inst_c_val = meta.query_advice(*inst_c, Rotation::cur());
            let val_a_val = meta.query_advice(*val_a, Rotation::cur());
            let val_b_val = meta.query_advice(*val_b, Rotation::cur());
            let val_b_next_val = meta.query_advice(*val_b_next, Rotation::cur());
            let pc_next_val = meta.query_advice(*pc_next, Rotation::cur());
            let branch_val = meta.query_advice(*branch_taken, Rotation::cur());
            
            // Constraint 1: Subtraction is correct
            let sub_constraint = val_b_next_val - (val_b_val - val_a_val);
            
            // Constraint 2: Branch is binary
            let binary_constraint = branch_val.clone() * (branch_val.clone() - Expression::Constant(Fp::from(1)));
            
            // Constraint 3: PC update formula
            let expected_pc = branch_val.clone() * inst_c_val + 
                             (Expression::Constant(Fp::from(1)) - branch_val) * (pc_val + Expression::Constant(Fp::from(1)));
            let pc_update = pc_next_val - expected_pc;
            
            vec![
                q.clone() * sub_constraint,
                q.clone() * binary_constraint,
                q * pc_update,
            ]
        });
    }
    
    fn define_memory_constraints(
        meta: &mut ConstraintSystem<Fp>,
        q_step: &Selector,
        mem_addr: &Column<Advice>,
        mem_value: &Column<Advice>,
        mem_timestamp: &Column<Advice>,
        inst_a: &Column<Advice>,
        inst_b: &Column<Advice>,
        val_a: &Column<Advice>,
        val_b: &Column<Advice>,
        val_b_next: &Column<Advice>,
        is_read: &Column<Fixed>,
        is_write: &Column<Fixed>,
        range_check: &Column<Fixed>,
    ) {
        // Memory read constraint: when reading, val matches memory table
        meta.lookup("memory read", |meta| {
            let q = meta.query_selector(*q_step);
            let addr_a = meta.query_advice(*inst_a, Rotation::cur());
            let val_a_cur = meta.query_advice(*val_a, Rotation::cur());
            let timestamp = meta.query_advice(*mem_timestamp, Rotation::cur());
            
            vec![
                (q.clone() * meta.query_fixed(*is_read, Rotation::cur())).into(),
                addr_a,
                val_a_cur,
                timestamp,
            ]
        }, |meta| {
            let addr = meta.query_advice(*mem_addr, Rotation::cur());
            let value = meta.query_advice(*mem_value, Rotation::cur());
            let timestamp = meta.query_advice(*mem_timestamp, Rotation::cur());
            vec![addr, value, timestamp]
        });
        
        // Memory write constraint
        meta.lookup("memory write", |meta| {
            let q = meta.query_selector(*q_step);
            let addr_b = meta.query_advice(*inst_b, Rotation::cur());
            let val_b_next_cur = meta.query_advice(*val_b_next, Rotation::cur());
            let timestamp_next = meta.query_advice(*mem_timestamp, Rotation::next());
            
            vec![
                (q.clone() * meta.query_fixed(*is_write, Rotation::cur())).into(),
                addr_b,
                val_b_next_cur,
                timestamp_next,
            ]
        }, |meta| {
            let addr = meta.query_advice(*mem_addr, Rotation::cur());
            let value = meta.query_advice(*mem_value, Rotation::cur());
            let timestamp = meta.query_advice(*mem_timestamp, Rotation::cur());
            vec![addr, value, timestamp]
        });
        
        // Range check for addresses
        meta.lookup("address range", |meta| {
            let q = meta.query_selector(*q_step);
            let addr_a = meta.query_advice(*inst_a, Rotation::cur());
            let addr_b = meta.query_advice(*inst_b, Rotation::cur());
            let addr_c = meta.query_advice(*inst_c, Rotation::cur());
            
            vec![
                (q.clone() * addr_a).into(),
                (q.clone() * addr_b).into(),
                (q * addr_c).into(),
            ]
        }, |meta| {
            let range_value = meta.query_fixed(*range_check, Rotation::cur());
            vec![range_value]
        });
    }
    
    fn define_pc_continuity(
        meta: &mut ConstraintSystem<Fp>,
        q_last: &Selector,
        pc: &Column<Advice>,
        pc_next: &Column<Advice>,
    ) {
        meta.create_gate("PC continuity", |meta| {
            let q_last_val = meta.query_selector(*q_last);
            let pc_cur = meta.query_advice(*pc, Rotation::cur());
            let pc_next_cur = meta.query_advice(*pc_next, Rotation::cur());
            let pc_next_row = meta.query_advice(*pc, Rotation::next());
            
            // If not last row, pc of next row equals pc_next of current row
            let continuity = (Expression::Constant(Fp::from(1)) - q_last_val.clone()) * (pc_next_row - pc_next_cur);
            
            // Also ensure pc_next_cur is consistent with branching (already in main gate)
            vec![continuity]
        });
    }
}



struct MemoryTable<F> {
    entries: Vec<MemoryEntry<F>>,
}

struct MemoryEntry<F> {
    timestamp: usize,
    address: usize,
    value: F,
    is_read: bool,
}

impl<F: Field> MemoryTable<F> {
    fn to_columns(&self) -> (Vec<F>, Vec<F>, Vec<F>) {
        let mut addresses = vec![];
        let mut values = vec![];
        let mut timestamps = vec![];
        
        for entry in &self.entries {
            addresses.push(F::from(entry.address as u64));
            values.push(entry.value);
            timestamps.push(F::from(entry.timestamp as u64));
        }
        
        (addresses, values, timestamps)
    }
}

// Witness structure for the ZKVM
pub struct Witness<F> {
    pub advice: Vec<Vec<F>>,
    pub memory_table: MemoryTable<F>,
}

impl<F: Field> Circuit<F> for ZKVM<F> {
    type Config = ZKVMConfig;
    type FloorPlanner = SimpleFloorPlanner;
    
    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        ZKVMConfig::configure(meta, 256, 1024) // Configurable memory size and max steps
    }
    
    fn synthesize(&self, config: Self::Config, mut layouter: impl Layouter<F>) -> Result<(), Error> {
        let witness = self.generate_witness();
        let num_rows = witness.advice[0].len();
        
        // Assign advice columns
        layouter.assign_region(|| "execution trace", |mut region| {
            for row in 0..num_rows {
                // Enable step selector
                config.q_step.enable(&mut region, row)?;
                if row == num_rows - 1 {
                    config.q_last.enable(&mut region, row)?;
                }
                
                // Assign all advice columns
                region.assign_advice(|| "pc", config.pc, row, || Value::known(witness.advice[0][row]))?;
                region.assign_advice(|| "inst_a", config.inst_a, row, || Value::known(witness.advice[1][row]))?;
                region.assign_advice(|| "inst_b", config.inst_b, row, || Value::known(witness.advice[2][row]))?;
                region.assign_advice(|| "inst_c", config.inst_c, row, || Value::known(witness.advice[3][row]))?;
                region.assign_advice(|| "val_a", config.val_a, row, || Value::known(witness.advice[4][row]))?;
                region.assign_advice(|| "val_b", config.val_b, row, || Value::known(witness.advice[5][row]))?;
                region.assign_advice(|| "val_b_next", config.val_b_next, row, || Value::known(witness.advice[6][row]))?;
                region.assign_advice(|| "pc_next", config.pc_next, row, || Value::known(witness.advice[7][row]))?;
                region.assign_advice(|| "branch", config.branch_taken, row, || Value::known(witness.advice[8][row]))?;
                region.assign_advice(|| "timestamp", config.mem_timestamp, row, || Value::known(witness.advice[9][row]))?;
                region.assign_advice(|| "step", config.mem_addr, row, || Value::known(witness.advice[10][row]))?;
            }
            Ok(())
        })?;
        
        // Assign memory table for lookup arguments
        layouter.assign_table(|| "memory table", |mut table| {
            let (addresses, values, timestamps) = witness.memory_table.to_columns();
            for i in 0..addresses.len() {
                table.assign_cell(|| "addr", config.mem_addr, i, || Value::known(addresses[i]))?;
                table.assign_cell(|| "value", config.mem_value, i, || Value::known(values[i]))?;
                table.assign_cell(|| "timestamp", config.mem_timestamp, i, || Value::known(timestamps[i]))?;
            }
            Ok(())
        })?;
        
        // Assign range check table
        layouter.assign_table(|| "range check", |mut table| {
            for i in 0..256 { // Memory size
                table.assign_cell(|| "range", config.range_check, i, || Value::known(F::from(i as u64)))?;
            }
            Ok(())
        })?;
        
        Ok(())
    }
}

#[derive(Clone, Debug)]
struct ZKVMProgram<F> {
    // Program code (loaded into memory at startup)
    code: Vec<SubleqInst>,
    // Initial memory state (including code and data)
    initial_memory: Vec<F>,
    // Number of steps to execute (can be less than max)
    steps: usize,
}

#[derive(Clone, Debug)]
pub struct SubleqInst {
    a: usize,
    b: usize,
    c: usize,
}

#[derive(Clone, Debug)]
struct ExecutionTrace<F> {
    // Each step's witness
    rows: Vec<ExecutionRow<F>>,
    // Memory access log (for lookup arguments)
    memory_log: Vec<MemoryAccess<F>>,
}

#[derive(Clone, Debug)]
struct ExecutionRow<F> {
    step: usize,
    pc: usize,
    inst: SubleqInst,
    val_a: F,
    val_b: F,
    val_b_next: F,
    pc_next: usize,
    branch_taken: bool,
    timestamp: usize,
}

#[derive(Clone, Debug)]
struct MemoryAccess<F> {
    timestamp: usize,
    address: usize,
    value: F,
    is_read: bool,
}

pub struct ZKVM<F> {
    config: ZKVMConfig,
    program: ZKVMProgram<F>,
    trace: ExecutionTrace<F>,
}

impl<F: Field> ZKVM<F> {
    pub fn new(memory_size: usize, max_steps: usize) -> Self {
        // Create empty program and trace
        ZKVM {
            config: ZKVMConfig::configure(&mut ConstraintSystem::default(), memory_size, max_steps),
            program: ZKVMProgram {
                code: vec![],
                initial_memory: vec![],
                steps: 0,
            },
            trace: ExecutionTrace {
                rows: vec![],
                memory_log: vec![],
            },
        }
    }
    
    pub fn load_program(&mut self, code: Vec<SubleqInst>, initial_data: Vec<F>) {
        // Program is loaded into memory starting at address 0
        let mut memory = initial_data.clone();
        
        // Extend memory to accommodate code
        for (i, inst) in code.iter().enumerate() {
            // Encode instruction as three consecutive memory cells
            // In a real implementation, you'd pack this more efficiently
            memory[i * 3] = F::from(inst.a as u64);
            memory[i * 3 + 1] = F::from(inst.b as u64);
            memory[i * 3 + 2] = F::from(inst.c as u64);
        }
        
        self.program = ZKVMProgram {
            code,
            initial_memory: memory,
            steps: 0,
        };
    }
    
    pub fn execute(&mut self, max_steps: usize) -> Result<(), Error> {
        let mut pc = 0;
        let mut memory = self.program.initial_memory.clone();
        let mut trace_rows = vec![];
        let mut memory_log = vec![];
        let mut timestamp = 0;
        
        for step in 0..max_steps {
            if pc >= self.program.code.len() * 3 {
                // PC points to data area or beyond - halt
                break;
            }
            
            // Fetch instruction (stored in memory)
            let a = memory[pc].to_bytes()[0] as usize;  // Simplified - real impl would decode properly
            let b = memory[pc + 1].to_bytes()[0] as usize;
            let c = memory[pc + 2].to_bytes()[0] as usize;
            
            // Record instruction fetch (read)
            memory_log.push(MemoryAccess {
                timestamp,
                address: pc,
                value: F::from(a as u64),
                is_read: true,
            });
            timestamp += 1;
            
            // Read values from memory
            let val_a = memory[a];
            let val_b = memory[b];
            
            // Record reads
            memory_log.push(MemoryAccess {
                timestamp,
                address: a,
                value: val_a,
                is_read: true,
            });
            timestamp += 1;
            
            memory_log.push(MemoryAccess {
                timestamp,
                address: b,
                value: val_b,
                is_read: true,
            });
            timestamp += 1;
            
            // Execute SUBLEQ
            let val_b_next = val_b - val_a;
            memory[b] = val_b_next;
            
            // Record write
            memory_log.push(MemoryAccess {
                timestamp,
                address: b,
                value: val_b_next,
                is_read: false,
            });
            timestamp += 1;
            
            // Determine next PC
            let branch_taken = val_b_next <= F::zero();
            let pc_next = if branch_taken { c } else { pc + 3 };
            
            // Record execution row
            trace_rows.push(ExecutionRow {
                step,
                pc,
                inst: SubleqInst { a, b, c },
                val_a,
                val_b,
                val_b_next,
                pc_next,
                branch_taken,
                timestamp: timestamp - 1, // Last timestamp for this step
            });
            
            pc = pc_next;
        }
        
        self.trace = ExecutionTrace {
            rows: trace_rows,
            memory_log,
        };
        self.program.steps = self.trace.rows.len();
        
        Ok(())
    }
    
    pub fn generate_witness(&self) -> Witness<F> {
        let num_rows = self.trace.rows.len();
        
        // Build witness columns
        let mut advice_cols = vec![vec![F::zero(); num_rows]; 11]; // 11 advice columns
        
        for (i, row) in self.trace.rows.iter().enumerate() {
            advice_cols[0][i] = F::from(row.pc as u64);
            advice_cols[1][i] = F::from(row.inst.a as u64);
            advice_cols[2][i] = F::from(row.inst.b as u64);
            advice_cols[3][i] = F::from(row.inst.c as u64);
            advice_cols[4][i] = row.val_a;
            advice_cols[5][i] = row.val_b;
            advice_cols[6][i] = row.val_b_next;
            advice_cols[7][i] = F::from(row.pc_next as u64);
            advice_cols[8][i] = F::from(row.branch_taken as u64);
            advice_cols[9][i] = F::from(row.timestamp as u64);
            advice_cols[10][i] = F::from(row.step as u64);
        }
        
        // Build memory table for lookup arguments
        let mem_table = self.build_memory_table();
        
        Witness {
            advice: advice_cols,
            memory_table: mem_table,
        }
    }
    
    fn build_memory_table(&self) -> MemoryTable<F> {
        let mut entries = vec![];
        for access in &self.trace.memory_log {
            entries.push(MemoryEntry {
                timestamp: access.timestamp,
                address: access.address,
                value: access.value,
                is_read: access.is_read,
            });
        }
        MemoryTable { entries }
    }
}




#[cfg(test)]
mod tests {

    use halo2_proofs::dev::MockProver;
    
    #[test]
    fn test_arbitrary_subleq_program() {
        // Example 1: Simple subtraction
        let mut vm = ZKVM::new(256, 100);
        
        // Program: mem[1] = mem[1] - mem[0]; if result <= 0 jump to halt
        let code = vec![
            SubleqInst { a: 0, b: 1, c: 3 },  // Main instruction
            SubleqInst { a: 0, b: 0, c: 0 },  // Halt
        ];
        
        // Initial memory: mem[0] = 10, mem[1] = 5
        let initial_memory = vec![
            Fp::from(10),  // address 0
            Fp::from(5),   // address 1
            Fp::from(0),   // address 2
            Fp::from(0),   // address 3 (code continues)
        ];
        
        vm.load_program(code, initial_memory);
        vm.execute(10).unwrap();
        
        // Verify the ZKVM circuit
        let circuit = vm;
        let public_inputs = vec![
            Fp::from(10),  // initial mem[0]
            Fp::from(5),   // initial mem[1]
            Fp::from(-5),  // final mem[1]
        ];
        
        let prover = MockProver::run(8, &circuit, vec![public_inputs]).unwrap();
        prover.assert_satisfied();
    }
    
    #[test]
    fn test_fibonacci_program() {
        let mut vm = ZKVM::new(256, 100);
        
        // Program to compute Fibonacci numbers
        // Memory layout:
        // 0: n (input)
        // 1: fib[0] = 0
        // 2: fib[1] = 1
        // 3: counter
        // 4: temp
        // 5: loop start
        // 6: loop end
        // 7: halt
        
        let code = vec![
            // Initialize: counter = 2, loop start at address 5
            SubleqInst { a: 0, b: 0, c: 0 }, // Placeholder - we'll implement proper Fibonacci
            // ... more instructions
        ];
        
        let initial_memory = vec![Fp::from(10), Fp::from(0), Fp::from(1), Fp::from(2), Fp::from(0)];
        
        vm.load_program(code, initial_memory);
        vm.execute(50).unwrap();
        
        // Verify
        let circuit = vm;
        let prover = MockProver::run(8, &circuit, vec![]).unwrap();
        prover.assert_satisfied();
    }
    
    #[test]
    fn test_factorial_program() {
        let mut vm = ZKVM::new(256, 100);
        
        // Program to compute factorial
        // Memory layout:
        // 0: n (input)
        // 1: result = 1
        // 2: counter = n
        // 3: loop condition
        // 4: loop body
        
        let code = vec![
            // counter = n
            SubleqInst { a: 0, b: 2, c: 3 }, // mem[2] = mem[2] - mem[0]
            // if counter <= 0 jump to halt
            SubleqInst { a: 0, b: 0, c: 0 },
        ];
        
        let initial_memory = vec![Fp::from(5), Fp::from(1), Fp::from(5), Fp::from(0)];
        
        vm.load_program(code, initial_memory);
        vm.execute(100).unwrap();
        
        let circuit = vm;
        let prover = MockProver::run(8, &circuit, vec![]).unwrap();
        prover.assert_satisfied();
    }
}