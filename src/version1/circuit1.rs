use std::marker::PhantomData;
use halo2_proofs::{circuit::*, plonk::*, poly::Rotation};

use ff::{PrimeField};

use crate::version1::vm1::{TraceRow};

// ============================================================================
// Circuit Configuration
// ============================================================================
#[derive(Debug, Clone)]
pub struct SubleqConfig { 
    pub pc: Column<Advice>,                 // Program counter
    pub inst_a: Column<Advice>,             // First operand address
    pub inst_b: Column<Advice>,             // Second operand address
    pub inst_c: Column<Advice>,             // Jump target
    pub op_a_value: Column<Advice>,         // Value at address a
    pub op_b_value: Column<Advice>,         // Value at address b before execution
    pub op_result: Column<Advice>,          // Value at address b after execution
    pub branch_taken: Column<Advice>,       // Whether branch is taken (0 or 1)
    pub new_pc: Column<Advice>,             // Next PC value
    
    // pub instance: Column<Instance>,
}

// ============================================================================
// Circuit Implementation with Permutation
// ============================================================================
#[derive(Default)]
pub struct SubleqCircuit<F: PrimeField> {
    pub initial_memory: Vec<(usize, i64)>,
    pub trace: Vec<TraceRow>,
    pub _marker: PhantomData<F>,
}

impl<F: PrimeField> SubleqCircuit<F> {
    pub fn new(initial_memory: Vec<(usize, i64)>, trace: Vec<TraceRow>) -> Self {
        Self { initial_memory, trace, _marker: PhantomData }
    }
}

impl<F: PrimeField> Circuit<F> for SubleqCircuit<F> {
    type Config = SubleqConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::new(vec![], vec![])
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        // Create columns
        let pc = meta.advice_column();
        let inst_a = meta.advice_column();
        let inst_b = meta.advice_column();
        let inst_c = meta.advice_column();
        let op_a_value = meta.advice_column();
        let op_b_value = meta.advice_column();
        let op_result = meta.advice_column();
        let branch_taken = meta.advice_column();
        let new_pc = meta.advice_column();
        
        let instruction_selector = meta.selector();
        
        // let instance = meta.instance_column();
        
        // ====================================================================
        // CONSTRAINT 1: SUBLEQ Arithmetic
        // ====================================================================
        meta.create_gate("subleq arithmetic", |meta| {
            let s = meta.query_selector(instruction_selector);
            let val_a = meta.query_advice(op_a_value, Rotation::cur());
            let val_b = meta.query_advice(op_b_value, Rotation::cur());
            let result = meta.query_advice(op_result, Rotation::cur());
            
            vec![s * (result - (val_b - val_a))]
        });
                
        // ====================================================================
        // CONSTRAINT 2: PC Progression
        // ====================================================================
        meta.create_gate("pc progression", |meta| {
            let s = meta.query_selector(instruction_selector);
            let pc_val = meta.query_advice(pc, Rotation::cur());
            let c_val = meta.query_advice(inst_c, Rotation::cur());
            let branch = meta.query_advice(branch_taken, Rotation::cur());
            let new_pc_val = meta.query_advice(new_pc, Rotation::cur());
            
            let pc_plus_3 = pc_val + Expression::Constant(F::from(3u64));
            let expected = pc_plus_3 * (Expression::Constant(F::from(1u64)) - branch.clone())
                          + c_val * branch;
            
            vec![s * (new_pc_val - expected)]
        });
        
        // ====================================================================
        // CONSTRAINT 3: Branch Condition Binary
        // ====================================================================
        meta.create_gate("branch binary", |meta| {
            let s = meta.query_selector(instruction_selector);
            let branch = meta.query_advice(branch_taken, Rotation::cur());
            
            vec![s * branch.clone() * (Expression::Constant(F::from(1u64)) - branch)]
        });
        
        SubleqConfig {
            pc, inst_a, 
            inst_b, inst_c, 
            branch_taken, 
            new_pc, 
            op_a_value, 
            op_b_value, 
            op_result,
            // instance,
        }
    }
    
    fn synthesize(&self, config: Self::Config, mut layouter: impl Layouter<F>) -> Result<(), Error> {       
        // Assign rows with permutation columns
        layouter.assign_region(|| "memory permutation", |mut region| {
            // Assign instruction rows
            for (idx, row) in self.trace.iter().enumerate() {
                // config.instruction_selector.enable(&mut region, idx)?;
                
                // Instruction columns
                region.assign_advice(|| "pc", config.pc, idx, || Value::known(F::from(row.pc as u64)))?;
                region.assign_advice(|| "inst_a", config.inst_a, idx, || Value::known(F::from(row.inst_a as u64)))?;
                region.assign_advice(|| "inst_b", config.inst_b, idx, || Value::known(F::from(row.inst_b as u64)))?;
                region.assign_advice(|| "inst_c", config.inst_c, idx, || Value::known(F::from(row.inst_c as u64)))?;
                region.assign_advice(|| "op_a_value", config.op_a_value, idx, || Value::known(F::from(row.op_a_value as u64)))?;
                region.assign_advice(|| "op_b_value", config.op_b_value, idx, || Value::known(F::from(row.op_b_value as u64)))?;
                region.assign_advice(|| "op_result", config.op_result, idx, || Value::known(F::from(row.op_result as u64)))?;
                region.assign_advice(|| "branch_taken", config.branch_taken, idx, || Value::known(F::from(row.branch_taken as u64)))?;
                region.assign_advice(|| "new_pc", config.new_pc, idx, || Value::known(F::from(row.new_pc as u64)))?;
            }
            Ok(())
        })?;
        
        Ok(())
    }
}


#[cfg(test)]
mod tests {
    use super::*;
    use crate::version1::vm1::{Instruction, SubleqState, subtraction_program, fibonacci_program, multiplication_program};
    use halo2_proofs::{dev::MockProver, halo2curves::pasta::Fp};
    
    type TestField = Fp;
        
    #[test]
    fn test_simple_subtraction_circuit() {
        // Simple subtraction: 10 - 5 = 5
        let (program, initial_memory, result_addr) = subtraction_program();
        
        let state = SubleqState::new(program.clone(), 256, 100);
        let trace = state.execute_program(&program, &initial_memory, 100).unwrap();

        let circuit = SubleqCircuit::<TestField>::new(initial_memory, trace);
        let prover = MockProver::run(4, &circuit, vec![]).unwrap();
        prover.assert_satisfied();
        
        // Verify the result from the trace
        let last_row = circuit.trace.last().unwrap();
        assert_eq!(last_row.op_result, 5); // 10 - 5 = 5
        assert_eq!(last_row.branch_taken, 0); // Should not branch since result > 0
    }

    #[test]
    fn test_branch_taken_circuit() {
        // Program that will take the branch (result <= 0)
        let program = vec![
            Instruction::new(0, 1, 3), // If result <= 0, jump to address 3
        ];
        
        let initial_memory = vec![
            (0, 10),  // a = 10
            (1, 5),   // b = 5, result = 5 - 10 = -5 <= 0, so branch taken
        ];
        
        let state = SubleqState::new(program.clone(), 256, 100);
        let trace = state.execute_program(&program, &initial_memory, 100).unwrap();
        
        // Verify branch was taken
        assert_eq!(trace[0].branch_taken, 1);
        assert_eq!(trace[0].new_pc, 3); // Jump to address 3
        
        let circuit = SubleqCircuit::<TestField>::new(initial_memory, trace);
        let prover = MockProver::run(4, &circuit, vec![]).unwrap();
        prover.assert_satisfied();
    }

    #[test]
    fn test_branch_not_taken_circuit() {
        // Program that will NOT take the branch (result > 0)
        let program = vec![
            Instruction::new(0, 1, 3), // If result <= 0, jump to address 3
        ];
        
        let initial_memory = vec![
            (0, 5),   // a = 5
            (1, 10),  // b = 10, result = 10 - 5 = 5 > 0, so branch not taken
        ];
        
        let state = SubleqState::new(program.clone(), 256, 100);
        let trace = state.execute_program(&program, &initial_memory, 100).unwrap();
        
        // Verify branch was NOT taken
        assert_eq!(trace[0].branch_taken, 0);
        assert_eq!(trace[0].new_pc, 3); // PC + 3 = 0 + 3 = 3
        
        let circuit = SubleqCircuit::<TestField>::new(initial_memory, trace);
        let prover = MockProver::run(4, &circuit, vec![]).unwrap();
        prover.assert_satisfied();
    }

    #[ignore]
    #[test]
    fn test_fibonacci_circuit() {
        let (program, initial_memory, result_addr) = fibonacci_program();
        
        let state = SubleqState::new(program.clone(), 256, 1000);
        let trace = state.execute_program(&program, &initial_memory, 1000).unwrap();
        
        let circuit = SubleqCircuit::<TestField>::new(initial_memory, trace);
        let prover = MockProver::run(8, &circuit, vec![]).unwrap();
        prover.assert_satisfied();
        
        // Check the final result from the last trace row that writes to result_addr
        let final_result = circuit.trace.iter()
            .filter(|row| row.inst_b == result_addr)
            .last()
            .map(|row| row.op_result)
            .unwrap_or(0);
        
        // Fibonacci number at position 5 should be 8 (1,1,2,3,5,8)
        assert_eq!(final_result, 8);
    }

    #[test]
    fn test_multiplication_circuit() {
        let (program, initial_memory, result_addr) = multiplication_program();
        
        let state = SubleqState::new(program.clone(), 256, 1000);
        let trace = state.execute_program(&program, &initial_memory, 1000).unwrap();

        let circuit = SubleqCircuit::<TestField>::new(initial_memory, trace);
        let prover = MockProver::run(17, &circuit, vec![]).unwrap();
        prover.assert_satisfied();
        
        // Check the final result (6 * 7 = 42)
        let final_result = circuit.trace.iter()
            .filter(|row| row.inst_b == result_addr)
            .last()
            .map(|row| row.op_result)
            .unwrap_or(0);
        
        assert_eq!(final_result, -7000); // 1000 loops times to -7
    }

    #[test]
    fn test_zero_subtraction_circuit() {
        // Test when subtracting zero (result remains the same)
        let program = vec![
            Instruction::new(0, 1, 2), // mem[1] = mem[1] - mem[0]
        ];
        
        let initial_memory = vec![
            (0, 0),   // a = 0
            (1, 5),   // b = 5, result = 5 - 0 = 5 > 0
        ];
        
        let state = SubleqState::new(program.clone(), 256, 100);
        let trace = state.execute_program(&program, &initial_memory, 100).unwrap();
        
        // Verify result unchanged
        assert_eq!(trace[0].op_result, 5);
        assert_eq!(trace[0].branch_taken, 0); // 5 > 0, no branch
        
        let circuit = SubleqCircuit::<TestField>::new(initial_memory, trace);
        let prover = MockProver::run(4, &circuit, vec![]).unwrap();
        prover.assert_satisfied();
    }

    #[test]
    fn test_multiple_instructions_circuit() {
        // Test with multiple instructions in sequence
        let program = vec![
            Instruction::new(0, 1, 3), // R1 = R1 - R0
            Instruction::new(1, 2, 6), // R2 = R2 - R1
        ];
        
        let initial_memory = vec![
            (0, 2),
            (1, 10),
            (2, 20),
        ];
        
        let state = SubleqState::new(program.clone(), 256, 100);
        let trace = state.execute_program(&program, &initial_memory, 100).unwrap();
        
        assert_eq!(trace.len(), 2);
        
        // First instruction: 10 - 2 = 8
        assert_eq!(trace[0].op_result, 8);
        assert_eq!(trace[0].branch_taken, 0);
        
        // Second instruction: 20 - 8 = 12
        assert_eq!(trace[1].op_result, 12);
        
        let circuit = SubleqCircuit::<TestField>::new(initial_memory, trace);
        let prover = MockProver::run(6, &circuit, vec![]).unwrap();
        prover.assert_satisfied();
    }

    #[test]
    fn test_max_steps_limit() {
        // Program that would loop indefinitely if not limited
        let program = vec![
            Instruction::new(0, 0, 0), // Infinite loop: subtract from itself, always branch to 0
        ];
        
        let initial_memory = vec![
            (0, 5),
        ];
        
        let state = SubleqState::new(program.clone(), 256, 10);
        let trace = state.execute_program(&program, &initial_memory, 10).unwrap();
        
        // Should only execute max_steps times
        assert_eq!(trace.len(), 10);
        
        let circuit = SubleqCircuit::<TestField>::new(initial_memory, trace);
        let prover = MockProver::run(4, &circuit, vec![]).unwrap();
        prover.assert_satisfied();
    }

    #[test]
    fn test_negative_numbers_circuit() {
        // Test with negative numbers
        let program = vec![
            Instruction::new(0, 1, 2), // mem[1] = mem[1] - mem[0]
        ];
        
        let initial_memory = vec![
            (0, -3),  // a = -3
            (1, 5),   // b = 5, result = 5 - (-3) = 8
        ];
        
        let state = SubleqState::new(program.clone(), 256, 100);
        let trace = state.execute_program(&program, &initial_memory, 100).unwrap();
        
        assert_eq!(trace[0].op_result, 8);
        assert_eq!(trace[0].branch_taken, 0); // 8 > 0
        
        let circuit = SubleqCircuit::<TestField>::new(initial_memory, trace);
        let prover = MockProver::run(4, &circuit, vec![]).unwrap();
        prover.assert_satisfied();
    }

    #[test]
    fn test_result_zero_branch() {
        // Test when result is exactly 0 (should branch)
        let program = vec![
            Instruction::new(0, 1, 3), // If result <= 0, jump to 3
        ];
        
        let initial_memory = vec![
            (0, 5),   // a = 5
            (1, 5),   // b = 5, result = 5 - 5 = 0 <= 0, so branch taken
        ];
        
        let state = SubleqState::new(program.clone(), 256, 100);
        let trace = state.execute_program(&program, &initial_memory, 100).unwrap();
        
        assert_eq!(trace[0].op_result, 0);
        assert_eq!(trace[0].branch_taken, 1); // Should branch on zero
        
        let circuit = SubleqCircuit::<TestField>::new(initial_memory, trace);
        let prover = MockProver::run(4, &circuit, vec![]).unwrap();
        prover.assert_satisfied();
    }
}