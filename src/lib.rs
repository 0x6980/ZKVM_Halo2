pub mod vm;
pub mod circuit;
pub mod memory_table;
mod new_impl;
#[cfg(test)]
mod tests {
    use super::*;
    use crate::vm::{Instruction};
    use halo2_proofs::{dev::MockProver, halo2curves::pasta::Fp};
    
    type TestField = Fp;
        
    #[test]
    fn test_simple_circuit() {
        // Create a simple program: R1 = R1 - R0
        let program = vec![
            Instruction::new(0, 1, 2),
        ];
        
        // Initialize VM and run
        let mut vm = SubleqVM::new(program, 10, 100)
            .with_initial_memory(vec![3, 10, 0]);
        
        let trace = vm.run().unwrap();
        // Create circuit
        let circuit = SubleqCircuit::<TestField>::new(trace, vm.get_initial_memory(), vec![]);
        
        // Test with mock prover
        let prover = MockProver::run(4, &circuit, vec![]).unwrap();
        prover.assert_satisfied();
    }

    #[test]
    fn test_jump_circuit() {
        // Program that jumps
        let program = vec![
            Instruction::new(0, 1, 2), // Should jump if result <= 0
            Instruction::new(2, 3, 4), // This should be skipped
        ];
        
        let mut vm = SubleqVM::new(program, 10, 100)
            .with_initial_memory(vec![2, 5, 0, 0]); // 5 - 2 = 3 no jump
        
        let trace = vm.run().unwrap();
        
        let circuit = SubleqCircuit::<TestField>::new(trace, vm.get_final_memory(), vec![]);
        let prover = MockProver::run(5, &circuit, vec![]).unwrap();
        prover.assert_satisfied();
    }

    #[test]
    fn test_zero_subtraction() {
        // Test when subtracting zero (no change, positive result)
        let program = vec![
            Instruction::new(0, 1, 2), // mem[1] = mem[1] - mem[0]
        ];
        
        let mut vm = SubleqVM::new(program, 10, 100)
            .with_initial_memory(vec![0, 5, 0]); // mem[0] = 0
        
        let trace = vm.run().unwrap();

        // Debug: print trace
        println!("Trace: {:?}", trace);
        
        let circuit = SubleqCircuit::<TestField>::new(trace.clone(), vm.get_final_memory(), vec![]);
        let prover = MockProver::run(4, &circuit, vec![]).unwrap();
        prover.assert_satisfied();
        
        assert_eq!(vm.get_final_memory()[1], 5); // Unchanged
        assert_eq!(trace[0].cond, 0); // 5 > 0, no jump
    }

        #[test]
    fn test_simple_program_with_memory_consistency() {
        let program = vec![
            Instruction::new(0, 1, 2),
        ];
        
        let mut vm = SubleqVM::new(program, 10, 100)
            .with_initial_memory(vec![3, 10, 0]);
        
        let trace = vm.run().unwrap();
        let initial_memory = vm.get_initial_memory();
        let circuit = SubleqCircuit::<TestField>::new(trace, initial_memory, vec![]);
        
        let prover = MockProver::run(8, &circuit, vec![]).unwrap();
        prover.assert_satisfied();
    }

    #[test]
    fn test_initial_memory_preserved() {
        let program = vec![
            Instruction::new(0, 1, 2),
        ];
        
        let mut vm = SubleqVM::new(program, 10, 100)
            .with_initial_memory(vec![7, 3, 0]);
        
        let trace = vm.run().unwrap();
        let initial_memory = vm.get_initial_memory();
        
        // Verify initial memory is correct
        assert_eq!(initial_memory[0], 7);
        assert_eq!(initial_memory[1], 3);
        
        let circuit = SubleqCircuit::<TestField>::new(trace, initial_memory, vec![]);
        let prover = MockProver::run(8, &circuit, vec![]).unwrap();
        prover.assert_satisfied();
    }
}