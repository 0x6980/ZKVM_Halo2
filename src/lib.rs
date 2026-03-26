pub mod vm;
pub mod circuit;

use halo2_proofs::{
    circuit::{Layouter, SimpleFloorPlanner, Value},
    plonk::{Circuit, ConstraintSystem, Error},
    poly::Rotation,
};
use ff::PrimeField;

use crate::vm::TraceRow;
use crate::circuit::{Field, SubleqChip, SubleqConfig};

/// Main Subleq ZKVM Circuit
#[derive(Default, Clone)]
pub struct SubleqCircuit<F: Field> {
    trace: Vec<TraceRow>,
    public_inputs: Vec<F>, // e.g., initial memory hash, final memory hash
}

impl<F: Field> SubleqCircuit<F> {
    pub fn new(trace: Vec<TraceRow>, public_inputs: Vec<F>) -> Self {
        Self { trace, public_inputs }
    }
}

impl<F: Field> Circuit<F> for SubleqCircuit<F> {
    type Config = SubleqConfig;
    type FloorPlanner = SimpleFloorPlanner;
    
    fn without_witnesses(&self) -> Self {
        Self::new(vec![], vec![])
    }
    
    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        // Create advice columns
        let pc = meta.advice_column();
        let a = meta.advice_column();
        let b = meta.advice_column();
        let c = meta.advice_column();
        let mem_a = meta.advice_column();
        let mem_b_before = meta.advice_column();
        let mem_b_after = meta.advice_column();
        let next_pc = meta.advice_column();
        let cond = meta.advice_column();
        
        // Instance column for public inputs
        // let instance = meta.instance_column();
        
        // Fixed column for constants
        let constants = meta.fixed_column();
        
        SubleqChip::configure(
            meta,
            pc, a, b, c,
            mem_a, 
            mem_b_before, 
            mem_b_after,
            next_pc, cond,
            // instance,
            constants,
        )
    }
    
    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let chip = SubleqChip::new(config);
        
        // Assign the trace
        chip.assign_trace(layouter.namespace(|| "trace"), &self.trace)?;
        
        // TODO: Add public input constraints (e.g., memory consistency)
        
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::vm::{SubleqVM, Instruction};
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
        let circuit = SubleqCircuit::<TestField>::new(trace, vec![]);
        
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
        
        let circuit = SubleqCircuit::<TestField>::new(trace, vec![]);
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
        
        let circuit = SubleqCircuit::<TestField>::new(trace.clone(), vec![]);
        let prover = MockProver::run(4, &circuit, vec![]).unwrap();
        prover.assert_satisfied();
        
        assert_eq!(vm.get_final_memory()[1], 5); // Unchanged
        assert_eq!(trace[0].cond, 0); // 5 > 0, no jump
    }


}