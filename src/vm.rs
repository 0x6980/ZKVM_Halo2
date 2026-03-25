use std::collections::HashMap;

/// Subleq instruction: mem[b] -= mem[a]; if mem[b] <= 0 { pc = c } else { pc += 1 }
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Instruction {
    pub a: usize,
    pub b: usize,
    pub c: usize,
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
    pub mem_a: i64,          // Value at address a before execution
    pub mem_b_before: i64,   // Value at address b before execution
    pub mem_b_after: i64,    // Value at address b after execution
    pub next_pc: usize,      // Next program counter
    pub cond: u8,            // 1 if mem_a_before <= 0, else 0
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
    pc: usize,
    program: Vec<Instruction>,
    trace: Vec<TraceRow>,
    max_steps: usize,
}

impl SubleqVM {
    pub fn new(program: Vec<Instruction>, memory_size: usize, max_steps: usize) -> Self {
        Self {
            memory: vec![0; memory_size],
            pc: 0,
            program,
            trace: Vec::new(),
            max_steps,
        }
    }

    pub fn with_initial_memory(mut self, initial_memory: Vec<i64>) -> Self {
        let size = self.memory.len();
        self.memory[..initial_memory.len().min(size)].copy_from_slice(&initial_memory[..size.min(initial_memory.len())]);
        self
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
        self.memory[b] = mem_b_before - mem_a;
        let mem_b_after = self.memory[b];
        
        // Determine next PC
        let cond = if mem_b_after <= 0 { 1 } else { 0 };
        let next_pc = if cond == 1 { c } else { self.pc + 1 };
        
        // Record trace
        self.trace.push(TraceRow {
            pc: self.pc,
            a,
            b,
            c,
            mem_a,
            mem_b_before,
            mem_b_after,
            next_pc,
            cond,
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
    fn test_simple_subleq() {
        // Program: R0 = R0 - R1; if R0 <= 0 jump to end
        // This subtracts 3 from 5, result 2 (positive, so continue)
        let program = vec![
            Instruction::new(0, 1, 2), // addr0 -= addr1; if addr0 <= 0 goto 2
            Instruction::new(0, 2, 3), // addr0 -= addr2; halt
        ];
        
        let mut vm = SubleqVM::new(program, 10, 100)
            .with_initial_memory(vec![5, 3, 0]);
        
        let trace = vm.run().unwrap();
        
        assert_eq!(trace.len(), 2);
        assert_eq!(vm.get_final_memory()[0], 2); // 5 - 3 = 2
        assert_eq!(trace[0].cond, 0); // 5 > 0, so no jump
    }
    
    #[test]
    fn test_jump() {
        // Program: R0 = R0 - R1; if R0 <= 0 jump to end
        // This subtracts 7 from 5, result -2 (negative, so jump)
        let program = vec![
            Instruction::new(0, 1, 2), // addr0 -= addr1; if addr0 <= 0 goto 2
            Instruction::new(0, 2, 3), // This should be skipped
        ];
        
        let mut vm = SubleqVM::new(program, 10, 100)
            .with_initial_memory(vec![5, 7, 0]);
        
        let trace = vm.run().unwrap();
        
        assert_eq!(trace.len(), 1);
        assert_eq!(vm.get_final_memory()[0], -2);
        assert_eq!(trace[0].cond, 1); // 5 > 0? No, 5-7 = -2, so condition met
    }
}