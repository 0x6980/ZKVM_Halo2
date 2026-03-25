use halo2_proofs::{
    circuit::{Chip, Layouter, Region, SimpleFloorPlanner, Value},
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Expression, Fixed, Instance, Selector},
    poly::Rotation,
};

use ff::PrimeField;
use std::marker::PhantomData;

use crate::vm::TraceRow;

/// Field element wrapper for our circuit
pub trait Field: PrimeField + From<u64> {}
impl<F> Field for F where F: PrimeField + From<u64> + From<i64> {}

/// Configuration for our Subleq circuit
#[derive(Debug, Clone)]
pub struct SubleqConfig {
    // Advice columns
    pub pc: Column<Advice>,
    pub a: Column<Advice>,
    pub b: Column<Advice>,
    pub c: Column<Advice>,
    pub mem_a: Column<Advice>,
    pub mem_b_before: Column<Advice>,
    pub mem_b_after: Column<Advice>,
    pub next_pc: Column<Advice>,
    pub cond: Column<Advice>,
    
    // Instance column for public inputs
    pub instance: Column<Instance>,
    
    // Fixed column for constants
    pub constants: Column<Fixed>,
    
    // Selectors
    pub subleq_gate: Selector,
    pub pc_transition_gate: Selector,
}

/// Chip implementing Subleq constraints
pub struct SubleqChip<F: Field> {
    config: SubleqConfig,
    _marker: PhantomData<F>,
}

impl<F: Field> SubleqChip<F> {
    pub fn new(config: SubleqConfig) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }
    
    /// Configure the circuit
    pub fn configure(
        meta: &mut ConstraintSystem<F>,
        pc: Column<Advice>,
        a: Column<Advice>,
        b: Column<Advice>,
        c: Column<Advice>,
        mem_a: Column<Advice>,
        mem_b_before: Column<Advice>,
        mem_b_after: Column<Advice>,
        next_pc: Column<Advice>,
        cond: Column<Advice>,
        instance: Column<Instance>,
        constants: Column<Fixed>,
    ) -> SubleqConfig {
        // Enable advice columns
        meta.enable_equality(pc);
        meta.enable_equality(a);
        meta.enable_equality(b);
        meta.enable_equality(c);
        meta.enable_equality(mem_a);
        meta.enable_equality(mem_b_before);
        meta.enable_equality(mem_b_after);
        meta.enable_equality(next_pc);
        meta.enable_equality(cond);
        
        let subleq_gate = meta.selector();
        let pc_transition_gate = meta.selector();
        
        // Gate 1: Subleq operation constraint
        // mem_b_after = mem_b_before - mem_a
        meta.create_gate("subleq operation", |meta| {
            let s = meta.query_selector(subleq_gate);
            let mem_a = meta.query_advice(mem_a, Rotation::cur());
            let mem_b_before = meta.query_advice(mem_b_before, Rotation::cur());
            let mem_b_after = meta.query_advice(mem_b_after, Rotation::cur());
            
            vec![s * (mem_b_before - mem_a - mem_b_after)]
        });
        
        // Gate 2: PC transition constraint
        // next_pc = cond * c + (1 - cond) * (pc + 1)
        meta.create_gate("pc transition", |meta| {
            let s = meta.query_selector(pc_transition_gate);
            let pc = meta.query_advice(pc, Rotation::cur());
            let c = meta.query_advice(c, Rotation::cur());
            let cond = meta.query_advice(cond, Rotation::cur());
            let next_pc = meta.query_advice(next_pc, Rotation::cur());
            
            let one = Expression::Constant(F::from(1u64));
            let pc_plus_one = pc + one.clone();
            let expected_next_pc = cond.clone() * c + (one.clone() - cond) * pc_plus_one;
            
            vec![s * (next_pc - expected_next_pc)]
        });
        
        SubleqConfig {
            pc,
            a,
            b,
            c,
            mem_a,
            mem_b_before,
            mem_b_after,
            next_pc,
            cond,
            instance,
            constants,
            subleq_gate,
            pc_transition_gate,
        }
    }
    
    /// Assign witness values from execution trace
    pub fn assign_trace(
        &self,
        mut layouter: impl Layouter<F>,
        trace: &[TraceRow],
    ) -> Result<(), Error> {
        layouter.assign_region(
            || "assign trace",
            |mut region| {
                for (i, row) in trace.iter().enumerate() {
                    // Enable gates for this row
                    self.config.subleq_gate.enable(&mut region, i)?;
                    self.config.pc_transition_gate.enable(&mut region, i)?;
                    
                    // Assign advice columns
                    region.assign_advice(|| "pc", self.config.pc, i, || Value::known(F::from(row.pc as u64)))?;
                    region.assign_advice(|| "a", self.config.a, i, || Value::known(F::from(row.a as u64)))?;
                    region.assign_advice(|| "b", self.config.b, i, || Value::known(F::from(row.b as u64)))?;
                    region.assign_advice(|| "c", self.config.c, i, || Value::known(F::from(row.c as u64)))?;
                    region.assign_advice(|| "mem_a", self.config.mem_a, i, || Value::known(F::from(row.mem_a as i64)))?;
                    region.assign_advice(|| "mem_b_before", self.config.mem_b_before, i, || Value::known(F::from(row.mem_b_before as i64)))?;
                    region.assign_advice(|| "mem_b_after", self.config.mem_b_after, i, || Value::known(F::from(row.mem_b_after as i64)))?;
                    region.assign_advice(|| "next_pc", self.config.next_pc, i, || Value::known(F::from(row.next_pc as u64)))?;
                    region.assign_advice(|| "cond", self.config.cond, i, || Value::known(F::from(row.cond as u64)))?;
                }
                Ok(())
            },
        )
    }
}