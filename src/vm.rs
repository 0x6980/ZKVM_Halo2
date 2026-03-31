use std::collections::HashMap;

/// Subleq instruction: mem[b] -= mem[a]; if mem[b] <= 0 { pc = c } else { pc += 1 }
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Instruction {
    pub a: usize, // Source address
    pub b: usize, // Destination address (also condition)
    pub c: usize, // Jump target
}

impl Instruction {
    pub fn new(a: usize, b: usize, c: usize) -> Self {
        Self { a, b, c }
    }
}

/// Execution trace row
#[derive(Debug, Clone, PartialEq)]
pub struct TraceRow {
    pub pc: usize,           // Program counter
    pub a: usize,            // Operand a
    pub b: usize,            // Operand b
    pub c: usize,            // Operand c (jump target)
    pub mem_a: i64,          // Value at address a 
    pub mem_b_before: i64,   // Value at address b before execution
    pub mem_b_after: i64,    // Value at address b after execution
    pub next_pc: usize,      // Next program counter
    pub cond: u8,            // 1 if mem_b_after <= 0, else 0
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

impl Default for TraceRow {
    fn default() -> Self {
        Self {
            pc: 0,
            a: 0,
            b: 0,
            c: 0,
            mem_a: 0,
            mem_b_before: 0,
            mem_b_after: 0,
            next_pc: 0,
            cond: 0,
        }
    }
}

/// Subleq Virtual Machine
pub struct SubleqVM {
    memory: Vec<i64>,
    initial_memory: Vec<i64>,  // Store initial memory for circuit
    pc: usize,
    program: Vec<Instruction>,
    trace: Vec<TraceRow>,
    max_steps: usize,
}

impl SubleqVM {
    pub fn new(program: Vec<Instruction>, memory_size: usize, max_steps: usize) -> Self {
        Self {
            memory: vec![0; memory_size],
            initial_memory: vec![0; memory_size],
            pc: 0,
            program,
            trace: Vec::new(),
            max_steps,
        }
    }

    pub fn with_initial_memory(mut self, initial_memory: Vec<i64>) -> Self {
        let size = self.memory.len();
        // Store initial memory
        self.initial_memory = vec![0; size];
        self.initial_memory[..initial_memory.len().min(size)].copy_from_slice(
            &initial_memory[..size.min(initial_memory.len())]
        );
        // Set current memory
        self.memory[..initial_memory.len().min(size)].copy_from_slice(
            &initial_memory[..size.min(initial_memory.len())]
        );
        self
    }

    pub fn get_initial_memory(&self) -> Vec<i64> {
        self.initial_memory.clone()
    }

    /// Execute a single step
    fn step(&mut self) -> bool {
        if self.pc >= self.program.len() {
            return false; // Program finished
        }

        let instruction = self.program[self.pc];
        let a = instruction.a;
        let b = instruction.b;
        let c = instruction.c;

        // Ensure memory bounds
        if a >= self.memory.len() || b >= self.memory.len() {
            return false;
        }

        let mem_a = self.memory[a];
        let mem_b_before = self.memory[b];
        
        // Execute Subleq: mem[b] = mem[b] - mem[a]
        let mem_b_after = mem_b_before - mem_a;
        self.memory[b] = mem_b_after;
        
        // Determine next PC
        let cond = if mem_b_after <= 0 { 1 } else { 0 };
        let next_pc = if cond == 1 { c } else { self.pc + 1 };
        
        // Record trace
        self.trace.push(TraceRow {
            pc: self.pc,
            a: a,
            b: b,
            c: c,
            mem_a: mem_a,
            mem_b_before: mem_b_before,
            mem_b_after: mem_b_after,
            next_pc: next_pc,
            cond: cond,
        });
        
        self.pc = next_pc;
        true
    }

    /// Run the VM and return the trace
    pub fn run(&mut self) -> Result<Vec<TraceRow>, &'static str> {
        self.trace.clear();
        
        for _ in 0..self.max_steps {
            if !self.step() {
                break;
            }
        }
        
        if self.pc < self.program.len() && self.trace.len() >= self.max_steps {
            return Err("Maximum steps reached without halting");
        }
        
        Ok(self.trace.clone())
    }
    
    pub fn get_final_memory(&self) -> Vec<i64> {
        self.memory.clone()
    }
}


#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_vm_with_initial_memory() {
        let program = vec![Instruction::new(0, 1, 2)];
        let mut vm = SubleqVM::new(program, 10, 100)
            .with_initial_memory(vec![3, 10, 0]);
        
        let trace = vm.run().unwrap();
        assert_eq!(trace.len(), 1);
        assert_eq!(vm.get_final_memory()[1], 7);
        assert_eq!(vm.get_initial_memory()[0], 3);
        assert_eq!(vm.get_initial_memory()[1], 10);
    }
    
    #[test]
    fn test_new_vm() {
        let program = vec![Instruction::new(0, 1, 2)];
        let vm = SubleqVM::new(program, 10, 100);
        
        assert_eq!(vm.memory.len(), 10);
        assert_eq!(vm.pc, 0);
        assert_eq!(vm.program.len(), 1);
        assert_eq!(vm.trace.len(), 0);
        assert_eq!(vm.max_steps, 100);
        
        // All memory should be zero-initialized
        assert!(vm.memory.iter().all(|&x| x == 0));
    }

    #[test]
    fn test_with_initial_memory() {
        let program = vec![Instruction::new(0, 1, 2)];
        let vm = SubleqVM::new(program, 10, 100)
            .with_initial_memory(vec![1, 2, 3, 4, 5]);
        
        assert_eq!(vm.memory[0], 1);
        assert_eq!(vm.memory[1], 2);
        assert_eq!(vm.memory[2], 3);
        assert_eq!(vm.memory[3], 4);
        assert_eq!(vm.memory[4], 5);
        assert_eq!(vm.memory[5], 0); // Rest should be zero
    }

    #[test]
    fn test_with_initial_memory_overflow() {
        let program = vec![Instruction::new(0, 1, 2)];
        let vm = SubleqVM::new(program, 3, 100)
            .with_initial_memory(vec![1, 2, 3, 4, 5]); // Only first 3 should be taken
        
        assert_eq!(vm.memory[0], 1);
        assert_eq!(vm.memory[1], 2);
        assert_eq!(vm.memory[2], 3);
        assert_eq!(vm.memory.len(), 3);
    }

    #[test]
    fn test_simple_subtraction_no_jump() {
        // mem[1] = mem[1] - mem[0]; result positive (7), no jump
        let program = vec![Instruction::new(0, 1, 2)];
        let mut vm = SubleqVM::new(program, 10, 100)
            .with_initial_memory(vec![3, 10, 0]);
        
        let trace = vm.run().unwrap();
        
        assert_eq!(trace.len(), 1);
        assert_eq!(vm.get_final_memory()[1], 7); // 10 - 3 = 7
        assert_eq!(vm.get_final_memory()[0], 3); // source unchanged
        
        assert_eq!(trace[0].pc, 0);
        assert_eq!(trace[0].a, 0);
        assert_eq!(trace[0].b, 1);
        assert_eq!(trace[0].c, 2);
        assert_eq!(trace[0].mem_a, 3);
        assert_eq!(trace[0].mem_b_before, 10);
        assert_eq!(trace[0].mem_b_after, 7);
        assert_eq!(trace[0].cond, 0); // 7 > 0, no jump
        assert_eq!(trace[0].next_pc, 1);
    }

    #[test]
    fn test_subtraction_with_jump_negative() {
        // mem[1] = mem[1] - mem[0]; result negative (-2), jump
        let program = vec![Instruction::new(0, 1, 2)];
        let mut vm = SubleqVM::new(program, 10, 100)
            .with_initial_memory(vec![7, 5, 0]);
        
        let trace = vm.run().unwrap();
        
        assert_eq!(trace.len(), 1);
        assert_eq!(vm.get_final_memory()[1], -2); // 5 - 7 = -2
        assert_eq!(vm.get_final_memory()[0], 7);
        
        assert_eq!(trace[0].cond, 1); // -2 <= 0, jump
        assert_eq!(trace[0].next_pc, 2);
    }

    #[test]
    fn test_subtraction_with_jump_zero() {
        // mem[1] = mem[1] - mem[0]; result zero, jump
        let program = vec![Instruction::new(0, 1, 2)];
        let mut vm = SubleqVM::new(program, 10, 100)
            .with_initial_memory(vec![5, 5, 0]);
        
        let trace = vm.run().unwrap();
        
        assert_eq!(trace.len(), 1);
        assert_eq!(vm.get_final_memory()[1], 0); // 5 - 5 = 0
        assert_eq!(trace[0].cond, 1); // 0 <= 0, jump
        assert_eq!(trace[0].next_pc, 2);
    }

    #[test]
    fn test_multiple_instructions_no_jump() {
        // Execute multiple instructions without jumps
        let program = vec![
            Instruction::new(0, 1, 3), // mem[1] -= mem[0]
            Instruction::new(1, 2, 4), // mem[2] -= mem[1]
            Instruction::new(2, 3, 5), // mem[3] -= mem[2]
        ];
        
        let mut vm = SubleqVM::new(program, 10, 100)
            .with_initial_memory(vec![2, 10, 9, 5, 0]);
        
        let trace = vm.run().unwrap();
       
        assert_eq!(trace.len(), 3);
        
        // Check intermediate values
        assert_eq!(vm.get_final_memory()[1], 8); // 10 - 2 = 8
        assert_eq!(vm.get_final_memory()[2], 1); // 8 - 7 = 1
        assert_eq!(vm.get_final_memory()[3], 4); // 5 - 1 = 4
        
        // Check trace conditions
        assert_eq!(trace[0].cond, 0); // 8 > 0
        assert_eq!(trace[1].cond, 0); // 1 > 0 
        assert_eq!(trace[2].cond, 0); // 5 > 0
    }

    #[test]
    fn test_jump_skipping_instructions() {
        // Program where first instruction jumps over the second
        let program = vec![
            Instruction::new(0, 1, 3), // if mem[1] <= 0, jump to 3
            Instruction::new(1, 2, 4), // This should be skipped (PC 1)
            Instruction::new(2, 3, 5), // This should execute after jump (PC 2)
            Instruction::new(0, 4, 6), // This is at PC 3 (jump target)
        ];
        
        let mut vm = SubleqVM::new(program, 10, 100)
            .with_initial_memory(vec![10, 5, 0, 0, 0, 0]); // 5 - 10 = -5 <= 0, jump
        
        let trace = vm.run().unwrap();
        
        // Should execute 2 instructions: PC 0 and PC 3
        assert_eq!(trace.len(), 2);
        
        // First instruction at PC 0
        assert_eq!(trace[0].pc, 0);
        assert_eq!(trace[0].a, 0);
        assert_eq!(trace[0].b, 1);
        assert_eq!(trace[0].c, 3);
        assert_eq!(trace[0].mem_a, 10);
        assert_eq!(trace[0].mem_b_before, 5);
        assert_eq!(trace[0].mem_b_after, -5); // 5 - 10 = -5
        assert_eq!(trace[0].cond, 1); // -5 <= 0, so jump
        assert_eq!(trace[0].next_pc, 3); // Jump to PC 3
        
        // Second instruction at PC 3 (jump target)
        assert_eq!(trace[1].pc, 3);
        assert_eq!(trace[1].a, 0);
        assert_eq!(trace[1].b, 4);
        assert_eq!(trace[1].c, 6);
        assert_eq!(trace[1].mem_a, 10);
        assert_eq!(trace[1].mem_b_before, 0);
        assert_eq!(trace[1].mem_b_after, -10); // 0 - 10 = -10
        assert_eq!(trace[1].cond, 1); // -10 <= 0, jump
        assert_eq!(trace[1].next_pc, 6); // Jump to PC 6 (end)
        
        // Verify final memory state
        assert_eq!(vm.get_final_memory()[0], 10); // mem[0] unchanged (source for both instructions)
        assert_eq!(vm.get_final_memory()[1], -5); // Updated by first instruction
        assert_eq!(vm.get_final_memory()[2], 0);  // mem[2] unchanged (PC 1 skipped)
        assert_eq!(vm.get_final_memory()[3], 0);  // mem[3] unchanged (not accessed)
        assert_eq!(vm.get_final_memory()[4], -10); // Updated by second instruction at PC 3
    }

    #[test]
    fn test_jump_to_self_infinite_loop_prevention() {
        // Program that jumps to itself
        let program = vec![
            Instruction::new(0, 0, 0), // mem[0] -= mem[0]; result 0, jump to 0
        ];
        
        let mut vm = SubleqVM::new(program, 10, 100)
            .with_initial_memory(vec![5, 0, 0]);
        
        let result = vm.run();
        
        // Should hit max steps
        assert!(result.is_err());
        assert_eq!(result.unwrap_err(), "Maximum steps reached without halting");
        assert_eq!(vm.trace.len(), 100); // max_steps reached
    }

    #[test]
    fn test_memory_bound_checks() {
        let program = vec![
            Instruction::new(100, 101, 102), // Out of bounds addresses
        ];
        
        let mut vm = SubleqVM::new(program, 10, 100)
            .with_initial_memory(vec![1, 2, 3]);
        
        let trace = vm.run().unwrap();
        
        // Should stop immediately due to out of bounds
        assert_eq!(trace.len(), 0);
        assert_eq!(vm.pc, 0);
    }

    #[test]
    fn test_empty_program() {
        let program = vec![];
        let mut vm = SubleqVM::new(program, 10, 100)
            .with_initial_memory(vec![1, 2, 3]);
        
        let trace = vm.run().unwrap();
        
        assert_eq!(trace.len(), 0);
        assert_eq!(vm.pc, 0);
        assert_eq!(vm.get_final_memory()[0], 1);
        assert_eq!(vm.get_final_memory()[1], 2);
        assert_eq!(vm.get_final_memory()[2], 3);
    }

    #[test]
    fn test_program_completion() {
        let program = vec![
            Instruction::new(0, 1, 2),
            Instruction::new(1, 2, 3),
        ];
        
        let mut vm = SubleqVM::new(program, 10, 100)
            .with_initial_memory(vec![2, 5, 4]);
        
        let trace = vm.run().unwrap();
        
        // Both instructions should execute
        assert_eq!(trace.len(), 2);
        assert_eq!(vm.pc, 2); // PC = program length, execution finished
    }

    #[test]
    fn test_max_steps_limit() {
        let program = vec![
            Instruction::new(0, 0, 0), // Infinite loop
        ];
        
        let mut vm = SubleqVM::new(program, 10, 50)
            .with_initial_memory(vec![1, 0, 0]);
        
        let result = vm.run();
        
        assert!(result.is_err());
        assert_eq!(vm.trace.len(), 50);
    }

    #[test]
    fn test_multiple_jumps() {
        // Program with multiple conditional jumps
        // Jump targets must be valid instruction indices (0-3 in this case)
        let program = vec![
            Instruction::new(0, 1, 3), // PC 0: if mem[1] <= 0, jump to PC 3
            Instruction::new(1, 2, 3), // PC 1: if mem[2] <= 0, jump to PC 3
            Instruction::new(2, 3, 3), // PC 2: if mem[3] <= 0, jump to PC 3
            Instruction::new(0, 0, 4), // PC 3: halt (jump to PC 4, which is program length)
        ];
        
        let mut vm = SubleqVM::new(program, 10, 100)
            .with_initial_memory(vec![3, 2, 4, 1, 0]);
        // Initial memory:
        // mem[0] = 3 (source for PC 0 and PC 3)
        // mem[1] = 2
        // mem[2] = 4
        // mem[3] = 1
        
        let trace = vm.run().unwrap();
        
        // Let's trace execution:
        // PC 0: mem[1] = mem[1] - mem[0] = 2 - 3 = -1 (<=0, so jump to PC 3)
        // PC 3: mem[0] = mem[0] - mem[0] = 3 - 3 = 0 (<=0, so jump to PC 4, halt)
        
        // So only 2 instructions should execute: PC 0 and PC 3
        assert_eq!(trace.len(), 2);
        
        // Verify first instruction (PC 0)
        assert_eq!(trace[0].pc, 0);
        assert_eq!(trace[0].a, 0);
        assert_eq!(trace[0].b, 1);
        assert_eq!(trace[0].c, 3);
        assert_eq!(trace[0].mem_a, 3);
        assert_eq!(trace[0].mem_b_before, 2);
        assert_eq!(trace[0].mem_b_after, -1); // 2 - 3 = -1
        assert_eq!(trace[0].cond, 1); // -1 <= 0, so jump
        assert_eq!(trace[0].next_pc, 3);
        
        // Verify second instruction (PC 3)
        assert_eq!(trace[1].pc, 3);
        assert_eq!(trace[1].a, 0);
        assert_eq!(trace[1].b, 0);
        assert_eq!(trace[1].c, 4);
        assert_eq!(trace[1].mem_a, 3);
        assert_eq!(trace[1].mem_b_before, 3);
        assert_eq!(trace[1].mem_b_after, 0); // 3 - 3 = 0
        assert_eq!(trace[1].cond, 1); // 0 <= 0, so jump
        assert_eq!(trace[1].next_pc, 4);
        
        // Verify final memory state
        assert_eq!(vm.get_final_memory()[0], 0); // Updated by PC 3
        assert_eq!(vm.get_final_memory()[1], -1); // Updated by PC 0
        assert_eq!(vm.get_final_memory()[2], 4); // Unchanged (PC 1 never executed)
        assert_eq!(vm.get_final_memory()[3], 1); // Unchanged (PC 2 never executed)
    }

    #[test]
    fn test_negative_memory_values() {
        // Test with negative initial values
        let program = vec![
            Instruction::new(0, 1, 2), // mem[1] = mem[1] - mem[0]
        ];
        
        let mut vm = SubleqVM::new(program, 10, 100)
            .with_initial_memory(vec![-3, -5, 0]);
        
        let trace = vm.run().unwrap();
        
        // -5 - (-3) = -5 + 3 = -2
        assert_eq!(vm.get_final_memory()[1], -2);
        assert_eq!(trace[0].cond, 1); // -2 <= 0, jump
    }

    #[test]
    fn test_large_memory_operations() {
        let program = vec![
            Instruction::new(5, 10, 20),
            Instruction::new(15, 25, 30),
        ];
        
        let mut vm = SubleqVM::new(program, 50, 100)
            .with_initial_memory(vec![0; 50]);
        
        // Set some values
        vm.memory[5] = 100;
        vm.memory[10] = 500;
        vm.memory[15] = 200;
        vm.memory[25] = 300;
        
        let trace = vm.run().unwrap();
        
        assert_eq!(trace.len(), 2);
        assert_eq!(vm.get_final_memory()[10], 400); // 500 - 100 = 400
        assert_eq!(vm.get_final_memory()[25], 100); // 300 - 200 = 100
    }

    #[test]
    fn test_trace_consistency() {
        let program = vec![
            Instruction::new(0, 1, 3),
            Instruction::new(1, 2, 4),
        ];
        
        let mut vm = SubleqVM::new(program.clone(), 10, 100)
            .with_initial_memory(vec![2, 5, 3, 0]);
        
        let trace = vm.run().unwrap();
        
        // Verify trace consistency
        for i in 0..trace.len() - 1 {
            assert_eq!(trace[i].next_pc, trace[i + 1].pc);
        }
        
        // Verify each trace row has correct instruction
        for (i, row) in trace.iter().enumerate() {
            let instr = program[i];
            assert_eq!(row.a, instr.a);
            assert_eq!(row.b, instr.b);
            assert_eq!(row.c, instr.c);
        }
    }
}