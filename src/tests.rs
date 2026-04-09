
// ============================================================================
// tests.rs - Comprehensive test suite for SUBLEQ circuit
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use halo2_proofs::{dev::MockProver, halo2curves::pasta::Fp};
    use crate::vm::{
        Instruction, SubleqState, TraceAndMemoryAccessRow, 
        MemoryEventType, subtraction_program, fibonacci_program, multiplication_program
    };
    use crate::circuit::{SubleqCircuit, SubleqConfig};

    // ============================================================================
    // Helper Functions
    // ============================================================================

    /// Helper to create a circuit from program and initial memory
    fn create_circuit_from_program(
        program: &[Instruction],
        initial_memory: Vec<(usize, i64)>,
    ) -> SubleqCircuit<Fp> {
        let state = SubleqState::new();
        let trace_memory_accesses = state
            .execute_program(program, &initial_memory, 100)
            .expect("Program execution failed");
        
        SubleqCircuit::new(initial_memory, trace_memory_accesses)
    }

    /// Helper to verify circuit with given parameters
    fn verify_circuit(
        circuit: SubleqCircuit<Fp>,
        k: u32,
        expected_result: Option<i64>,
        result_addr: Option<usize>,
    ) {
        let prover = MockProver::run(k, &circuit, vec![]).unwrap();
        
        match prover.verify() {
            Ok(_) => {
                println!("✓ Circuit verified successfully!");
                if let (Some(expected), Some(addr)) = (expected_result, result_addr) {
                    // Verify final memory state if needed
                    let final_state = get_final_memory_state(&circuit);
                    if let Some(&value) = final_state.get(&addr) {
                        assert_eq!(value, expected, "Final memory value at address {} is {} but expected {}", 
                                  addr, value, expected);
                        println!("✓ Final memory[{}] = {} (expected: {})", addr, value, expected);
                    }
                }
            }
            Err(errors) => {
                println!("✗ Verification failed with {} errors:", errors.len());
                for (i, error) in errors.iter().enumerate() {
                    println!("  Error {}: {:?}", i, error);
                }
                panic!("Circuit verification failed");
            }
        }
    }

    /// Helper to extract final memory state from circuit (simplified)
    fn get_final_memory_state(circuit: &SubleqCircuit<Fp>) -> std::collections::HashMap<usize, i64> {
        let mut memory = std::collections::HashMap::new();
        
        // Initialize with initial memory
        for (addr, value) in &circuit.initial_memory {
            memory.insert(*addr, *value);
        }
        
        // Apply all writes from trace
        for row in &circuit.trace_memory_accesses {
            if row.op_type == MemoryEventType::Write {
                memory.insert(row.mem_addr, row.mem_value);
            }
        }
        
        memory
    }

    // ============================================================================
    // Test 1: Basic Subtraction
    // ============================================================================
    #[test]
    fn test_basic_subtraction() {
        println!("\n=== Test 1: Basic Subtraction (10 - 5 = 5) ===");
        
        let (program, initial_memory, result_addr) = subtraction_program();
        let circuit = create_circuit_from_program(&program, initial_memory);
        
        // Verify trace has correct number of rows (1 instruction = 3 rows)
        assert_eq!(circuit.trace_memory_accesses.len(), 3);
        
        // Verify operation types
        assert_eq!(circuit.trace_memory_accesses[0].op_type, MemoryEventType::ReadA);
        assert_eq!(circuit.trace_memory_accesses[1].op_type, MemoryEventType::ReadB);
        assert_eq!(circuit.trace_memory_accesses[2].op_type, MemoryEventType::Write);
        
        // Verify values
        assert_eq!(circuit.trace_memory_accesses[0].mem_value, 5);  // Read A: mem[1]=5
        assert_eq!(circuit.trace_memory_accesses[1].mem_value, 10); // Read B: mem[0]=10
        assert_eq!(circuit.trace_memory_accesses[2].mem_value, 5);  // Write: 10-5=5
        
        println!("{:?}", "!!!!!!!!!!!!!!!!!!!!!!!!!!");
        
        verify_circuit(circuit, 17, Some(5), Some(result_addr));
    }

    // ============================================================================
    // Test 2: Multiple Instructions with Memory Continuity
    // ============================================================================
    #[test]
    fn test_multiple_instructions() {
        println!("\n=== Test 2: Multiple Instructions with Memory Continuity ===");
        
        let program = vec![
            Instruction { a: 1, b: 0, c: 6 },  // mem[0] = 10 - 5 = 5
            Instruction { a: 0, b: 2, c: 9 },  // mem[2] = 0 - 5 = -5 (reads updated mem[0])
        ];
        
        let initial_memory = vec![
            (0, 10),
            (1, 5),
            (2, 0),
        ];
        
        let circuit = create_circuit_from_program(&program, initial_memory);
        
        // Should have 2 instructions * 3 = 6 rows
        assert_eq!(circuit.trace_memory_accesses.len(), 6);
        
        // Verify memory continuity: instruction 1 reads updated value from instruction 0
        // Instruction 0 writes to addr 0 at row 2 (timestamp 2)
        // Instruction 1 reads from addr 0 at row 3 (timestamp 3) - should see value 5
        assert_eq!(circuit.trace_memory_accesses[2].mem_addr, 0);
        assert_eq!(circuit.trace_memory_accesses[2].mem_value, 5);  // Write from inst 0
        assert_eq!(circuit.trace_memory_accesses[3].mem_addr, 0);
        assert_eq!(circuit.trace_memory_accesses[3].mem_value, 5);  // Read from inst 1
        
        verify_circuit(circuit, 15, Some(-5), Some(2));
    }

    // ============================================================================
    // Test 3: Branching Program
    // ============================================================================
    #[test]
    fn test_branching_program() {
        println!("\n=== Test 3: Branching Program ===");
        
        let program = vec![
            Instruction { a: 1, b: 0, c: 6 },  // mem[0] = 5 - 10 = -5 (negative, branch to 6)
            Instruction { a: 2, b: 3, c: 0 },  // This should be skipped
            Instruction { a: 4, b: 5, c: 0 },  // Jump target (pc=6 -> instruction index 2)
        ];
        
        let initial_memory = vec![
            (0, 5),
            (1, 10),
            (2, 100),
            (3, 200),
            (4, 1),
            (5, 2),
        ];
        
        let circuit = create_circuit_from_program(&program, initial_memory);
        
        // First instruction should branch
        assert_eq!(circuit.trace_memory_accesses[2].branch_taken, true);
        assert_eq!(circuit.trace_memory_accesses[2].new_pc, 6);
        
        // Only 2 instructions should execute (first and third) = 6 rows
        assert_eq!(circuit.trace_memory_accesses.len(), 6);
        
        // Second instruction (inst_id=1) should be the third instruction in program
        assert_eq!(circuit.trace_memory_accesses[3].inst_id, 1);
        assert_eq!(circuit.trace_memory_accesses[3].inst_a, 4);
        assert_eq!(circuit.trace_memory_accesses[3].inst_b, 5);
        
        verify_circuit(circuit, 15, Some(1), Some(5));
    }

    // ============================================================================
    // Test 4: Zero and Negative Values
    // ============================================================================
    #[test]
    fn test_zero_and_negative_values() {
        println!("\n=== Test 4: Zero and Negative Values ===");
        
        let program = vec![
            Instruction { a: 1, b: 0, c: 3 },  // 0 - (-5) = 5
            Instruction { a: 2, b: 3, c: 6 },  // -3 - 2 = -5
        ];
        
        let initial_memory = vec![
            (0, 0),
            (1, -5),
            (2, 2),
            (3, -3),
        ];
        
        let circuit = create_circuit_from_program(&program, initial_memory);
        
        // Verify arithmetic with negatives
        assert_eq!(circuit.trace_memory_accesses[2].mem_value, 5);   // 0 - (-5) = 5
        assert_eq!(circuit.trace_memory_accesses[5].mem_value, -5);  // -3 - 2 = -5
        
        verify_circuit(circuit, 15, Some(-5), Some(3));
    }

    // ============================================================================
    // Test 5: Fibonacci Program
    // ============================================================================
    // #[test]
    // fn test_fibonacci_program() {
    //     println!("\n=== Test 5: Fibonacci Program (5th Fibonacci number) ===");
        
    //     let (program, initial_memory, result_addr) = fibonacci_program();
    //     let circuit = create_circuit_from_program(&program, initial_memory);
        
    //     // Should have multiple instructions (the program has 10 instructions)
    //     assert!(circuit.trace_memory_accesses.len() > 0);
        
    //     println!("Executed {} instructions ({} memory accesses)", 
    //              circuit.trace_memory_accesses.len() / 3,
    //              circuit.trace_memory_accesses.len());
        
    //     verify_circuit(circuit, 50, None, None);
    // }

    // ============================================================================
    // Test 6: Multiplication Program
    // ============================================================================
    // #[test]
    // fn test_multiplication_program() {
    //     println!("\n=== Test 6: Multiplication Program (6 * 7 = 42) ===");
        
    //     let (program, initial_memory, result_addr) = multiplication_program();
    //     let circuit = create_circuit_from_program(&program, initial_memory);
        
    //     verify_circuit(circuit, 30, Some(42), Some(result_addr));
    // }

    // ============================================================================
    // Test 7: Large Program (Stress Test)
    // ============================================================================
    // #[test]
    // fn test_large_program() {
    //     println!("\n=== Test 7: Large Program (20 instructions) ===");
        
    //     let mut program = Vec::new();
    //     let mut initial_memory = vec![(0, 1000), (1, 1)];
        
    //     // Create a program that counts down from 1000 to 980
    //     for i in 0..20 {
    //         program.push(Instruction { a: 1, b: 0, c: (i + 1) * 3 });
    //         initial_memory.push((i + 2, 0));
    //     }
        
    //     let circuit = create_circuit_from_program(&program, initial_memory);
        
    //     assert_eq!(circuit.trace_memory_accesses.len(), 60); // 20 instructions * 3 rows
        
    //     // Verify decreasing pattern
    //     let mut expected_value = 1000;
    //     for i in 0..20 {
    //         let write_idx = i * 3 + 2;
    //         assert_eq!(circuit.trace_memory_accesses[write_idx].mem_value, expected_value - 1);
    //         expected_value -= 1;
    //     }
        
    //     verify_circuit(circuit, 100, Some(980), Some(0));
    // }

    // ============================================================================
    // Test 8: Memory Overwrite Verification
    // ============================================================================
    #[test]
    fn test_memory_overwrite() {
        println!("\n=== Test 8: Memory Overwrite Verification ===");
        
        let program = vec![
            Instruction { a: 2, b: 0, c: 3 },  // mem[0] = 100 - 50 = 50
            Instruction { a: 3, b: 0, c: 6 },  // mem[0] = 50 - 25 = 25 (overwrites)
            Instruction { a: 0, b: 1, c: 9 },  // mem[1] = 10 - 25 = -15 (reads updated mem[0])
        ];
        
        let initial_memory = vec![
            (0, 100),
            (1, 10),
            (2, 50),
            (3, 25),
        ];
        
        let circuit = create_circuit_from_program(&program, initial_memory);
        
        // Verify the overwrite sequence
        assert_eq!(circuit.trace_memory_accesses[2].mem_value, 50);   // First write: 50
        assert_eq!(circuit.trace_memory_accesses[5].mem_value, 25);   // Overwrite: 25
        assert_eq!(circuit.trace_memory_accesses[6].mem_value, 25);   // Reads the overwritten value
        
        verify_circuit(circuit, 20, Some(-15), Some(1));
    }

    // ============================================================================
    // Test 9: Edge Case - Reading Uninitialized Memory
    // ============================================================================
    #[test]
    fn test_uninitialized_memory() {
        println!("\n=== Test 9: Reading Uninitialized Memory (should read 0) ===");
        
        let program = vec![
            Instruction { a: 1, b: 0, c: 3 },  // mem[0] = 0 - 0 = 0
        ];
        
        let initial_memory = vec![
            (0, 0),  // Only initialize address 0
            // Address 1 is uninitialized, should read as 0
        ];
        
        let circuit = create_circuit_from_program(&program, initial_memory);
        
        // Uninitialized memory reads as 0
        assert_eq!(circuit.trace_memory_accesses[0].mem_value, 0);
        
        verify_circuit(circuit, 10, Some(0), Some(0));
    }

    // ============================================================================
    // Test 10: Complex Arithmetic Chain
    // ============================================================================
    // #[test]
    // fn test_complex_arithmetic_chain() {
    //     println!("\n=== Test 10: Complex Arithmetic Chain ===");
        
    //     let program = vec![
    //         Instruction { a: 1, b: 0, c: 3 },   // a = 100, b = 50 -> mem[0] = -50
    //         Instruction { a: 2, b: 3, c: 6 },   // c = 30, d = 20 -> mem[3] = -10
    //         Instruction { a: 0, b: 3, c: 9 },   // mem[3] = (-10) - (-50) = 40
    //         Instruction { a: 3, b: 4, c: 12 },  // mem[4] = 0 - 40 = -40
    //     ];
        
    //     let initial_memory = vec![
    //         (0, 50),
    //         (1, 100),
    //         (2, 30),
    //         (3, 20),
    //         (4, 0),
    //     ];
        
    //     let circuit = create_circuit_from_program(&program, initial_memory);
        
    //     // Verify the chain of operations
    //     assert_eq!(circuit.trace_memory_accesses[2].mem_value, -50);   // 50 - 100 = -50
    //     assert_eq!(circuit.trace_memory_accesses[5].mem_value, -10);   // 20 - 30 = -10
    //     assert_eq!(circuit.trace_memory_accesses[8].mem_value, 40);    // (-10) - (-50) = 40
    //     assert_eq!(circuit.trace_memory_accesses[11].mem_value, -40);   // 0 - 40 = -40
        
    //     verify_circuit(circuit, 25, Some(-40), Some(4));
    // }

    // ============================================================================
    // Test 11: Verify Constraint Violations (Should Fail)
    // ============================================================================
    #[test]
    #[should_panic(expected = "Circuit verification failed")]
    fn test_invalid_arithmetic() {
        println!("\n=== Test 11: Invalid Arithmetic (Expected to fail) ===");
        
        let program = vec![
            Instruction { a: 1, b: 0, c: 3 },
        ];
        
        let initial_memory = vec![(0, 10), (1, 5)];
        
        // Create circuit with correct trace
        let state = SubleqState::new();
        let mut trace = state.execute_program(&program, &initial_memory, 100).unwrap();
        
        // Corrupt the write value (should be 5, set to 100)
        trace[2].mem_value = 100;
        
        let circuit = SubleqCircuit::new(initial_memory, trace);
        verify_circuit(circuit, 10, None, None);
    }

    // ============================================================================
    // Test 12: Invalid Address (Should Fail)
    // ============================================================================
    #[test]
    #[should_panic(expected = "Circuit verification failed")]
    fn test_invalid_address() {
        println!("\n=== Test 12: Invalid Address (Expected to fail) ===");
        
        let program = vec![
            Instruction { a: 1, b: 0, c: 3 },
        ];
        
        let initial_memory = vec![(0, 10), (1, 5)];
        
        // Create circuit with correct trace
        let state = SubleqState::new();
        let mut trace = state.execute_program(&program, &initial_memory, 100).unwrap();
        
        // Corrupt the address (should be 1, set to 2)
        trace[0].mem_addr = 2;
        
        let circuit = SubleqCircuit::new(initial_memory, trace);
        verify_circuit(circuit, 10, None, None);
    }

    // ============================================================================
    // Test 13: Invalid Branch (Should Fail)
    // ============================================================================
    #[test]
    #[should_panic(expected = "Circuit verification failed")]
    fn test_invalid_branch() {
        println!("\n=== Test 13: Invalid Branch (Expected to fail) ===");
        
        let program = vec![
            Instruction { a: 1, b: 0, c: 9 },  // Result is -5, should branch
        ];
        
        let initial_memory = vec![(0, 5), (1, 10)];
        
        // Create circuit with correct trace
        let state = SubleqState::new();
        let mut trace = state.execute_program(&program, &initial_memory, 100).unwrap();
        
        // Set branch_taken to false when it should be true
        trace[2].branch_taken = false;
        
        let circuit = SubleqCircuit::new(initial_memory, trace);
        verify_circuit(circuit, 10, None, None);
    }

    // ============================================================================
    // Test 14: Performance Test with Many Instructions
    // ============================================================================
    #[test]
    fn test_performance_50_instructions() {
        println!("\n=== Test 14: Performance Test (50 instructions) ===");
        
        let mut program = Vec::new();
        let mut initial_memory = vec![(0, 500), (1, 1)];
        
        for i in 0..50 {
            program.push(Instruction { a: 1, b: 0, c: (i + 1) * 3 });
            initial_memory.push((i + 2, 0));
        }
        
        let start = std::time::Instant::now();
        let circuit = create_circuit_from_program(&program, initial_memory);
        let duration = start.elapsed();
        
        println!("  - Generated {} memory access rows in {:?}", 
                 circuit.trace_memory_accesses.len(), duration);
        println!("  - {} instructions executed", circuit.trace_memory_accesses.len() / 3);
        
        let start_verify = std::time::Instant::now();
        verify_circuit(circuit, 200, Some(450), Some(0));
        println!("  - Verification completed in {:?}", start_verify.elapsed());
    }

    // ============================================================================
    // Test 15: Verify Timestamp Monotonicity
    // ============================================================================
    #[test]
    fn test_timestamp_monotonicity() {
        println!("\n=== Test 15: Verify Timestamp Monotonicity ===");
        
        let program = vec![
            Instruction { a: 1, b: 0, c: 3 },
            Instruction { a: 2, b: 1, c: 6 },
        ];
        
        let initial_memory = vec![(0, 100), (1, 10), (2, 20)];
        
        let circuit = create_circuit_from_program(&program, initial_memory);
        
        // Verify timestamps are strictly increasing
        let mut prev_timestamp = 0;
        for (i, row) in circuit.trace_memory_accesses.iter().enumerate() {
            assert!(row.mem_timestamp > prev_timestamp, 
                    "Timestamp not increasing at row {}: {} <= {}", 
                    i, row.mem_timestamp, prev_timestamp);
            prev_timestamp = row.mem_timestamp;
        }
        
        println!("✓ All {} timestamps are strictly increasing", 
                 circuit.trace_memory_accesses.len());
        
        verify_circuit(circuit, 15, None, None);
    }
}

// ============================================================================
// Main test runner (optional)
// ============================================================================
// #[cfg(test)]
// mod test_runner {
//     use super::tests::*;

//     pub fn run_all_tests() {
//         println!("\n╔════════════════════════════════════════════════════════════════╗");
//         println!("║           SUBLEQ Circuit Test Suite - Comprehensive Tests      ║");
//         println!("╚════════════════════════════════════════════════════════════════╝");
        
//         test_basic_subtraction();
//         test_multiple_instructions();
//         test_branching_program();
//         test_zero_and_negative_values();
//         test_fibonacci_program();
//         test_multiplication_program();
//         test_large_program();
//         test_memory_overwrite();
//         test_uninitialized_memory();
//         test_complex_arithmetic_chain();
//         test_timestamp_monotonicity();
//         test_performance_50_instructions();
        
//         println!("\n╔════════════════════════════════════════════════════════════════╗");
//         println!("║                    ALL TESTS PASSED!                           ║");
//         println!("╚════════════════════════════════════════════════════════════════╝");
//     }
// }