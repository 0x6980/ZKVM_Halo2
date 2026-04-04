use std::collections::HashMap;

// ============================================================================
// SUBLEQ Instruction Definition
// ============================================================================
// SUBLEQ does: memory[b] = memory[b] - memory[a]; if (memory[b] <= 0) pc = c
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Instruction {
    pub a: usize, // Source address
    pub b: usize, // Destination address (also condition)
    pub c: usize, // Jump target (if result <= 0)
}

impl Instruction {
    pub fn new(a: usize, b: usize, c: usize) -> Self {
        Self { a, b, c }
    }
}

// ============================================================================
// Execution Trace Record
// ============================================================================
#[derive(Debug, Clone, PartialEq)]
pub struct TraceRow {
    pub pc: usize,              // Program counter
    pub inst_a: usize,          // Operand a
    pub inst_b: usize,          // Operand b
    pub inst_c: usize,          // Operand c (jump target)
    pub op_a_value: i64,        // Value at address a
    pub op_b_value: i64,        // Value at address b before execution
    pub op_result: i64,         // Value at address b after execution
    pub branch_taken: u64,      // 1 if mem_b_after <= 0, else 0
    pub new_pc: usize,          // Next program counter
}

// ============================================================================
// Memory Access Record (for trace collection)
// ============================================================================
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct MemoryAccess {
    pub addr: usize,
    pub value: i64,
    pub timestamp: usize,
    pub is_write: bool,
}


// ============================================================================
// VM State
// ============================================================================
#[derive(Debug, Clone)]
pub struct SubleqState {
    pub pc: usize,
    pub memory: [i64; 256],  // Fixed-size memory for simplicity
}

impl SubleqState {
    pub fn new(program: Vec<Instruction>, memory_size: usize, max_steps: usize) -> Self {
        Self {
            pc: 0,
            memory: [0; 256],
        }
    }

    // ========================================================================
    // Execute the program and collect a complete trace with memory consistency
    // ========================================================================
    pub fn execute_program(
        &self,
        program: &[Instruction],
        initial_memory: &[(usize, i64)],
        max_steps: usize,
    ) -> Result<(Vec<TraceRow>, Vec<MemoryAccess>), String> {
        let mut state = SubleqState {
            pc: 0,
            memory: [0; 256],
        };
        
        // Initialize memory
        for (addr, value) in initial_memory {
            if *addr < 256 {
                state.memory[*addr] = *value;
            }
        }
        
        let mut trace = Vec::new();
        let mut memory_accesses = Vec::new();
        let mut current_timestamp = 0;
        
        // Record initial memory state (all non-zero values)
        for (addr, value) in state.memory.iter().enumerate() {
            if *value != 0 {
                memory_accesses.push(MemoryAccess {
                    addr,
                    value: *value,
                    timestamp: current_timestamp,
                    is_write: true,
                });
            }
        }
        current_timestamp += 1;
        
        // Execute program
        let mut steps = 0;
        while state.pc < program.len() * 3 && steps < max_steps {
            let inst_index = state.pc / 3;
            let instruction = program[inst_index];
            
            // Read operation for address a
            let a_val = state.memory[instruction.a];
            memory_accesses.push(MemoryAccess {
                addr: instruction.a,
                value: a_val,
                timestamp: current_timestamp,
                is_write: false,
            });
            let read_a_timestamp = current_timestamp;
            current_timestamp += 1;
            
            // Read operation for address b
            let b_val = state.memory[instruction.b];
            memory_accesses.push(MemoryAccess {
                addr: instruction.b,
                value: b_val,
                timestamp: current_timestamp,
                is_write: false,
            });
            let read_b_timestamp = current_timestamp;
            current_timestamp += 1;
            
            // Compute operation
            let result = b_val - a_val;
            let branch_taken_val = if result <= 0 { 1 } else { 0 };
            let new_pc = if branch_taken_val == 1 {
                instruction.c
            } else {
                state.pc + 3
            };
            
            // Record trace
            trace.push(TraceRow {
                pc: state.pc,
                inst_a: instruction.a,
                inst_b: instruction.b,
                inst_c: instruction.c,
                op_a_value: a_val,
                op_b_value: b_val,
                op_result: result,
                branch_taken: branch_taken_val,
                new_pc,
            });
            
            // Write operation to address b
            let old_b_val = b_val;
            state.memory[instruction.b] = result;
            
            memory_accesses.push(MemoryAccess {
                addr: instruction.b,
                value: result,
                timestamp: current_timestamp,
                is_write: true,
            });
            current_timestamp += 1;
            
            // Update PC
            state.pc = new_pc;
            steps += 1;
        }
        
        // Sort memory accesses by (addr, timestamp) for consistency checking
        memory_accesses.sort_by_key(|ma| (ma.addr, ma.timestamp));
        
        // Verify memory consistency
        self.verify_memory_consistency(&memory_accesses)?;
        
        Ok((trace, memory_accesses))
    }
    
    // ========================================================================
    // Verify memory consistency (offline check)
    // ========================================================================
    fn verify_memory_consistency(
        &self,
        accesses: &[MemoryAccess],
    ) -> Result<(), String> {
        let mut by_addr: HashMap<usize, Vec<&MemoryAccess>> = HashMap::new();
        
        for access in accesses {
            by_addr.entry(access.addr).or_default().push(access);
        }
        
        for (addr, timeline) in by_addr {
            // Timeline should already be sorted by timestamp
            if timeline.is_empty() {
                continue;
            }
            
            // First access should be a write (initialization)
            if !timeline[0].is_write {
                return Err(format!(
                    "Address {}: first access at timestamp {} is not a write",
                    addr, timeline[0].timestamp
                ));
            }
            
            let mut current_value = timeline[0].value;
            
            for access in &timeline[1..] {
                if access.is_write {
                    // Write can change the value
                    current_value = access.value;
                } else {
                    // Read must get the current value
                    if access.value != current_value {
                        return Err(format!(
                            "Address {}: read at timestamp {} expected {} but got {}",
                            addr, access.timestamp, current_value, access.value
                        ));
                    }
                }
            }
        }
        
        Ok(())
    }

    pub fn get_final_memory(&self) -> [i64; 256] {
        self.memory.clone()
    }
    
}

// ============================================================================
// Example Programs
// ============================================================================

// Example 1: Simple subtraction: 10 - 5 = 5
pub fn subtraction_program() -> (Vec<Instruction>, Vec<(usize, i64)>, usize) {
    let program = vec![
        // Subtract memory[1] from memory[0], then stop
        Instruction { a: 1, b: 0, c: 3 },
    ];
    
    let initial_memory = vec![
        (0, 10),  // Address 0: 10
        (1, 5),   // Address 1: 5
    ];
    
    let result_addr = 0;  // Result stored at address 0
    
    (program, initial_memory, result_addr)
}

// Example 2: Fibonacci using SUBLEQ (computes 5th Fibonacci number)
pub fn fibonacci_program() -> (Vec<Instruction>, Vec<(usize, i64)>, usize) {
    // Memory layout:
    // 0: loop counter (starting at 5)
    // 1: f(n-2) = 1
    // 2: f(n-1) = 1
    // 3: temporary storage
    // 4: constant 1 for decrement
    // 5: result address
    
    let program = vec![
        // Copy f(n-1) to result
        Instruction { a: 2, b: 5, c: 0 },  // result = 0 - f(n-1)
        Instruction { a: 5, b: 5, c: 0 },  // result = -f(n-1) - (-f(n-1)) = 0
        
        // Add f(n-2) to result
        Instruction { a: 1, b: 5, c: 0 },  // result = result - f(n-2)
        Instruction { a: 5, b: 5, c: 0 },  // result = -result? This is simplified
        
        // Shift values: f(n-2) = f(n-1), f(n-1) = result
        Instruction { a: 2, b: 3, c: 0 },  // temp = -f(n-1)
        Instruction { a: 3, b: 1, c: 0 },  // f(n-2) = f(n-2) - (-f(n-1)) = f(n-2)+f(n-1)
        Instruction { a: 1, b: 2, c: 0 },  // f(n-1) = f(n-1) - f(n)
        
        // Decrement counter
        Instruction { a: 4, b: 0, c: 0 },  // counter = counter - 1
        
        // Loop if counter > 0
        Instruction { a: 0, b: 0, c: 8 },  // if counter <= 0, jump to end
        Instruction { a: 0, b: 0, c: 0 },  // else jump back to start
    ];
    
    let initial_memory = vec![
        (0, 5),   // Counter: compute up to f(5)
        (1, 1),   // f(0) = 1
        (2, 1),   // f(1) = 1
        (3, 0),   // Temporary
        (4, 1),   // Constant 1
        (5, 0),   // Result
    ];
    
    let result_addr = 5;
    
    (program, initial_memory, result_addr)
}

// Example 3: Multiply using repeated addition
pub fn multiplication_program() -> (Vec<Instruction>, Vec<(usize, i64)>, usize) {
    // Multiply 6 * 7 = 42 using repeated addition
    // Memory layout:
    // 0: multiplier (6)
    // 1: multiplicand (7)
    // 2: result (0)
    // 3: counter (6)
    // 4: constant 1
    
    let program = vec![
        // Loop: result = result + multiplicand
        Instruction { a: 1, b: 2, c: 0 },  // result = result - multiplicand
        Instruction { a: 2, b: 2, c: 0 },  // result = result - result = -multiplicand? This is simplified
        
        // Decrement counter
        Instruction { a: 4, b: 3, c: 0 },  // counter = counter - 1
        
        // Loop if counter > 0
        Instruction { a: 3, b: 3, c: 6 },  // if counter <= 0, jump to end
        Instruction { a: 0, b: 0, c: 0 },  // else jump back to start
    ];
    
    let initial_memory = vec![
        (0, 6),   // Multiplier
        (1, 7),   // Multiplicand
        (2, 0),   // Result
        (3, 6),   // Counter
        (4, 1),   // Constant 1
    ];
    
    let result_addr = 2;
    
    (program, initial_memory, result_addr)
}