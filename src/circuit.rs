use halo2_proofs::{
    circuit::{Chip, Layouter, Region, SimpleFloorPlanner, Value},
    plonk::{Advice, Circuit, Column, ConstraintSystem, Error, Expression, Fixed, Instance, Selector},
    poly::Rotation,
};

use ff::PrimeField;
use std::marker::PhantomData;

use crate::vm::TraceRow;
use crate::memory_table::{MemoryTraceColumns, MemoryConsistencyChip, MemoryTableConfig};

/// Field element wrapper for our circuit
pub trait Field: PrimeField {}
impl<F> Field for F where F: PrimeField {}

/// Configuration for our Subleq circuit
#[derive(Debug, Clone)]
pub struct SubleqConfig {
    // Instruction columns
    pub pc: Column<Advice>,                 // Program counter
    pub a: Column<Advice>,                  // First operand address
    pub b: Column<Advice>,                  // Second operand address
    pub c: Column<Advice>,                  // Jump target
    
    // Operation columns
    pub mem_a: Column<Advice>,              // Value at address a
    pub mem_b_before: Column<Advice>,       // Value at address b
    pub mem_b_after: Column<Advice>,        // b - a
    
    // Branch condition
    pub next_pc: Column<Advice>,            // Next PC value
    pub cond: Column<Advice>,               // Whether branch is taken (0 or 1)

    pub step: Column<Advice>,

    pub constants: Column<Fixed>,
    // Public inputs/outputs
    //pub instance: Column<Instance>,
    
    // Selectors
    pub subleq_gate: Selector,
    pub pc_transition_gate: Selector,
    pub cond_binary_gate: Selector,
    pub memory_selector: Selector, 

    pub memory_table: MemoryTableConfig,
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
        step: Column<Advice>,  // Add step column for memory consistency
        // instance: Column<Instance>,
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
        meta.enable_equality(step);
        
        let subleq_gate = meta.selector();
        let pc_transition_gate = meta.selector();
        let cond_binary_gate = meta.selector();
        let memory_selector = meta.selector();

        // Configure memory table
        let memory_table = MemoryTableConfig::configure(meta);
        
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
            
            let one = Expression::Constant(F::ONE);
            // next_pc = pc + 1 + cond * (c - pc - 1)
            let expected_next_pc = pc.clone() + one.clone() + cond.clone() * (c - pc - one);
            
            vec![s * (next_pc - expected_next_pc)]
        });


        // Gate 3: Enforce cond is binary (0 or 1)
        // cond * (cond - 1) = 0
        meta.create_gate("cond binary", |meta| {
            let s = meta.query_selector(cond_binary_gate);
            let cond = meta.query_advice(cond, Rotation::cur());
            
            vec![s * (cond.clone() * (cond - Expression::Constant(F::ONE)))]
        });

        // Add memory lookup constraints
        let trace_cols = MemoryTraceColumns::new(
            step, a, mem_a, b, mem_b_before, mem_b_after, memory_selector.clone()
        );
        let memory_chip = MemoryConsistencyChip::new(memory_table.clone());
        memory_chip.add_memory_lookups(meta, &trace_cols, &memory_table);

        SubleqConfig {
            pc: pc,
            a: a,
            b: b,
            c: c,
            mem_a: mem_a,
            mem_b_before: mem_b_before,
            mem_b_after: mem_b_after,
            next_pc: next_pc,
            cond: cond,
            // instance: instance,
            constants: constants,
            subleq_gate: subleq_gate,
            pc_transition_gate: pc_transition_gate,
            cond_binary_gate: cond_binary_gate,
            memory_selector,
            memory_table,
            step: step,
        }
    }
    
    /// Convert i64 to field element using from_u128
    fn to_field(val: i64) -> F {
        if val >= 0 {
            F::from_u128(val as u128)
        } else {
            // negative numbers are represented as -val = modulus - abs(val).
            let abs_val = (-val) as u128;
            let hex_str = F::MODULUS.strip_prefix("0x").unwrap_or(F::MODULUS);
            let modulus= u128::from_str_radix(hex_str, 16);
            F::from_u128(modulus.unwrap() - abs_val)

            // let modulus: u128 = F::MODULUS.into();
            // F::from_u128(modulus - (-val) as u128)
        }
    }
    
    /// Assign witness values from execution trace
    pub fn assign_trace(
        &self,
        mut layouter: impl Layouter<F>,
        trace: &[TraceRow],
        initial_memory: &[i64],
    ) -> Result<(), Error> {
        // Build memory table first
        let memory_chip = MemoryConsistencyChip::new(self.config.memory_table.clone());
        memory_chip.build_table(layouter.namespace(|| "memory table"), trace, initial_memory)?;

        layouter.assign_region(
            || "assign trace",
            |mut region| {
                println!("\n=== ASSIGNING TRACE ROWS ===");
                for (i, row) in trace.iter().enumerate() {
                    println!("Trace row {}: step={}, a={}, mem_a={}, b={}, before={}, after={}", 
                    i, i, row.a, row.mem_a, row.b, row.mem_b_before, row.mem_b_after);
                    // Enable gates for this row
                    self.config.subleq_gate.enable(&mut region, i)?;
                    self.config.pc_transition_gate.enable(&mut region, i)?;
                    self.config.cond_binary_gate.enable(&mut region, i)?;
                    self.config.memory_selector.enable(&mut region, i)?;
                    
                    // Assign advice columns
                    region.assign_advice(|| "pc", self.config.pc, i, || Value::known(F::from_u128(row.pc as u128)))?;
                    region.assign_advice(|| "a", self.config.a, i, || Value::known(F::from_u128(row.a as u128)))?;
                    region.assign_advice(|| "b", self.config.b, i, || Value::known(F::from_u128(row.b as u128)))?;
                    region.assign_advice(|| "c", self.config.c, i, || Value::known(F::from_u128(row.c as u128)))?;
                    region.assign_advice(|| "mem_a", self.config.mem_a, i, || Value::known(Self::to_field(row.mem_a as i64)))?;
                    region.assign_advice(|| "mem_b_before", self.config.mem_b_before, i, || Value::known(Self::to_field(row.mem_b_before as i64)))?;
                    region.assign_advice(|| "mem_b_after", self.config.mem_b_after, i, || Value::known(Self::to_field(row.mem_b_after as i64)))?;
                    region.assign_advice(|| "next_pc", self.config.next_pc, i, || Value::known(F::from_u128(row.next_pc as u128)))?;
                    region.assign_advice(|| "cond", self.config.cond, i, || Value::known(F::from_u128(row.cond as u128)))?;
                    region.assign_advice(|| "step", self.config.step, i, || Value::known(F::from_u128(row.cond as u128)))?;
                }
                Ok(())
            },
        )
    }
}


#[test]
fn test_field_conversion() {
    use halo2_proofs::halo2curves::pasta::Fp;
    
    let pos = Fp::from_u128(5);
    let neg_from_i64 = Fp::from_u128((-5i64) as u128);
    
    println!("Positive 5: {:?}", pos);
    println!("Negative -5 as u128: {:?}", (-5i64) as u128);
    println!("Negative -5 as field: {:?}", neg_from_i64);
    
    // Check if pos + neg = 0 in the field
    let sum = pos + neg_from_i64;
    println!("5 + (-5) = {:?}", sum);
    assert_eq!(sum, Fp::zero());
}