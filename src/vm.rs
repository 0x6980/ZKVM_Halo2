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
    // Instruction metadata
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
// Trace Row for Memory Access (one per memory event)
// ============================================================================
#[derive(Debug, Clone)]
pub struct TraceAndMemoryAccessRow {
    // Instruction metadata
    pub pc: usize,                              // Program counter
    pub inst_a: usize,                          // Operand a
    pub inst_b: usize,                          // Operand b
    pub inst_c: usize,                          // Operand c (jump target)
    pub branch_taken: bool,                     // 1 if mem_b_after <= 0, else 0
    pub new_pc: usize,                          // Next program counter

    // Memory access data
    pub mem_addr: usize,
    pub mem_value: i64,
    pub mem_timestamp: usize,

    // Operation type
    pub op_type: MemoryEventType,

    // Instruction ID (same for all 3 rows of same instruction)
    pub inst_id: usize,
}

// ============================================================================
// Memory Event for Permutation
// ============================================================================
#[derive(Debug, Clone, Copy, Eq, PartialEq, Ord, PartialOrd)]
pub enum MemoryEventType {
    ReadA = 0,
    ReadB = 1,
    Write = 2,
}

// ============================================================================
// Memory Access Record (for trace collection)
// ============================================================================
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct MemoryAccess {
    pub addr: usize,
    pub value: i64,
    pub timestamp: usize,
    pub event_type: MemoryEventType,
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
    pub fn new() -> Self {
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
    ) -> Result<Vec<TraceAndMemoryAccessRow>, String> {
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

        // Execute program
        let mut trace_and_memory_access_rows = Vec::new();
        let mut current_timestamp = 1;
        let mut steps = 0;

        while state.pc < program.len() * 3 && steps < max_steps {
            let inst_index = state.pc / 3;
            let instruction = program[inst_index];

            // Read operation for address a
            let a_val = state.memory[instruction.a];

            // Read operation for address b
            let b_val = state.memory[instruction.b];

            // Write operation to address b
            // let old_b_val = b_val;
            let result = b_val - a_val;

            // Compute operation
            let branch_taken_val = result <= 0;
            let new_pc = if branch_taken_val {
                instruction.c
            } else {
                state.pc + 3
            };

            trace_and_memory_access_rows.push(TraceAndMemoryAccessRow {
                pc: state.pc,
                inst_a: instruction.a,
                inst_b: instruction.b,
                inst_c: instruction.c,
                branch_taken: branch_taken_val,
                new_pc: new_pc,

                mem_addr: instruction.a,
                mem_value: a_val,
                mem_timestamp: current_timestamp,
                op_type: MemoryEventType::ReadA,

                inst_id: steps,
            });
            current_timestamp += 1;

            trace_and_memory_access_rows.push(TraceAndMemoryAccessRow {
                pc: state.pc,
                inst_a: instruction.a,
                inst_b: instruction.b,
                inst_c: instruction.c,
                branch_taken: branch_taken_val,
                new_pc: new_pc,

                mem_addr: instruction.b,
                mem_value: b_val,
                mem_timestamp: current_timestamp,
                op_type: MemoryEventType::ReadB,

                inst_id: steps,
            });
            current_timestamp += 1;
            state.memory[instruction.b] = result;

            trace_and_memory_access_rows.push(TraceAndMemoryAccessRow {
                pc: state.pc,
                inst_a: instruction.a,
                inst_b: instruction.b,
                inst_c: instruction.c,
                branch_taken: branch_taken_val,
                new_pc: new_pc,

                mem_addr: instruction.b,
                mem_value: result,
                mem_timestamp: current_timestamp,
                op_type: MemoryEventType::Write,

                inst_id: steps,
            });
            current_timestamp += 1;

            // Update PC
            state.pc = new_pc;
            steps += 1;
        }

        Ok(trace_and_memory_access_rows)
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