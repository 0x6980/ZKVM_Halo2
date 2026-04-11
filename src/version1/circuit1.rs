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
    
    pub instance: Column<Instance>,
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
        
        let instance = meta.instance_column();
        
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
        // CONSTRAINT 3: PC Progression
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
        // CONSTRAINT 4: Branch Condition Binary
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
            instance,
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
                region.assign_advice(|| "branch_taken", config.branch_taken, idx, || Value::known(F::from(row.branch_taken as u64)))?;
                region.assign_advice(|| "new_pc", config.new_pc, idx, || Value::known(F::from(row.new_pc as u64)))?;
            }
            Ok(())
        })?;

        
        Ok(())
    }
}