use halo2_proofs::{
    circuit::{Layouter, Value},
    plonk::{Advice, Column, ConstraintSystem, Expression, Error, Selector, TableColumn},
    poly::Rotation,
};
use ff::PrimeField;
use std::marker::PhantomData;

use crate::vm::TraceRow;

/// Memory table configuration
#[derive(Debug, Clone)]
pub struct MemoryTableConfig {
    // pub step: TableColumn,
    pub addr: TableColumn,
    pub value_before: TableColumn,
    pub value_after: TableColumn,
}

impl MemoryTableConfig {
    pub fn configure(meta: &mut ConstraintSystem<impl PrimeField>) -> Self {
        // let step = meta.lookup_table_column();
        let addr = meta.lookup_table_column();
        let value_before = meta.lookup_table_column();
        let value_after = meta.lookup_table_column();
        
        // meta.annotate_lookup_column(step, "step");
        // meta.annotate_lookup_column(addr, "address");
        // meta.annotate_lookup_column(value_before, "value_before");
        // meta.annotate_lookup_column(value_after, "value_after");

        Self { addr, value_before, value_after }
    }
}

/// Trace columns for memory lookups
#[derive(Debug, Clone)]
pub struct MemoryTraceColumns {
    // pub step: Column<Advice>,           // Step counter
     
    pub read_addr: Column<Advice>,      // Address a (read operation)
    pub read_value: Column<Advice>,     // mem_a value
    pub write_addr: Column<Advice>,     // Address b (write operation)
    pub write_before: Column<Advice>,   // mem_b_before
    pub write_after: Column<Advice>,    // mem_b_after
    pub memory_selector: Selector,
}

impl MemoryTraceColumns {
    pub fn new(
        // step: Column<Advice>,
        a: Column<Advice>,
        mem_a: Column<Advice>,
        b: Column<Advice>,
        mem_b_before: Column<Advice>,
        mem_b_after: Column<Advice>,
        memory_selector: Selector,
    ) -> Self {
        Self {
            // step,
            read_addr: a,
            read_value: mem_a,
            write_addr: b,
            write_before: mem_b_before,
            write_after: mem_b_after,
            memory_selector,
        }
    }
}

/// Memory consistency chip
pub struct MemoryConsistencyChip<F: PrimeField> {
    config: MemoryTableConfig,
    _marker: PhantomData<F>,
}

impl<F: PrimeField> MemoryConsistencyChip<F> {
    pub fn new(config: MemoryTableConfig) -> Self {
        Self { config, _marker: PhantomData }
    }
    
    fn to_field(val: i64) -> F {
        if val >= 0 {
            println!("{:?}", "ttttttttttttttttttttttttttttttttttttttttttttttt");
            println!("{:?}", val);
            F::from_u128(val as u128)
        } else {
            // let modulus: u128 = F::MODULUS.into();
            // F::from_u128(modulus - (-val) as u128)

            let abs_val = (-val) as u128;
            let hex_str = F::MODULUS.strip_prefix("0x").unwrap_or(F::MODULUS);
            let modulus= u128::from_str_radix(hex_str, 16);
            F::from_u128(modulus.unwrap() - abs_val)
        }
    }
    
    /// Build memory table from trace rows
    pub fn build_table(
        &self,
        mut layouter: impl Layouter<F>,
        trace: &[TraceRow],
        initial_memory: &[i64],
    ) -> Result<(), Error> {
        use std::collections::HashMap;
        
        // Initialize memory state with initial values
        let mut memory_state: HashMap<usize, i64> = HashMap::new();
        for (addr, &value) in initial_memory.iter().enumerate() {
            if value != 0 {
                memory_state.insert(addr, value);
            }
        }

        let mut table_rows: Vec<(usize, i64, i64)> = Vec::new();
        println!("{}", trace.len());
        println!("{}", "eeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee");
        for (step, row) in trace.iter().enumerate() {
            println!("Step {}: Processing instruction", step);
            // READ from address a
            let read_before = *memory_state.get(&row.a).unwrap_or(&0);
            println!("  READ: addr={}, before={}, trace_mem_a={}", row.a, read_before, row.mem_a);
            assert_eq!(read_before, row.mem_a, 
                "Memory inconsistency at step {}: read from addr {} expected {} got {}", 
                step, row.a, read_before, row.mem_a);
            table_rows.push((row.a, row.mem_a, row.mem_a));
            
            // WRITE to address b
            let write_before = *memory_state.get(&row.b).unwrap_or(&0);
            println!("  WRITE: addr={}, before={}, after={}, trace_before={}, trace_after={}", 
            row.b, write_before, row.mem_b_after, row.mem_b_before, row.mem_b_after);
            assert_eq!(write_before, row.mem_b_before,
                "Memory inconsistency at step {}: write to addr {} expected {} got {}", 
                step, row.b, write_before, row.mem_b_before);
            table_rows.push((row.b, row.mem_b_before, row.mem_b_after));
        }
        
        println!("\n=== TABLE ROWS ===");
        for (i, (addr, before, after)) in table_rows.iter().enumerate() {
            println!("Row {}: addr={}, before={}, after={}", i, addr, before, after);
        }
        // Assign table
        layouter.assign_table(
            || "memory table",
            |mut table| {
                for (idx, (addr, before, after)) in table_rows.iter().enumerate() {
                    println!("{:?}", Value::known(Self::to_field(*after)));
                    println!("{}", "rrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrrr");
                    // table.assign_cell(
                    //     || format!("step_{}", idx),
                    //     self.config.step,
                    //     idx,
                    //     || Value::known(F::from_u128(*step as u128)),
                    // )?;
                    table.assign_cell(
                        || format!("addr_{}", idx),
                        self.config.addr,
                        idx,
                        || Value::known(F::from_u128(*addr as u128)),
                    )?;
                    table.assign_cell(
                        || format!("before_{}", idx),
                        self.config.value_before,
                        idx,
                        || Value::known(Self::to_field(*before)),
                    )?;
                    table.assign_cell(
                        || format!("after_{}", idx),
                        self.config.value_after,
                        idx,
                        || Value::known(Self::to_field(*after)),
                    )?;
                }
                Ok(())
            },
        )
    }
    
    /// Add lookup constraints
    pub fn add_memory_lookups(
        &self,
        meta: &mut ConstraintSystem<F>,
        trace_cols: &MemoryTraceColumns,
        memory_config: &MemoryTableConfig,
    ) {
        // Lookup for READ operations
        meta.lookup("memory_read", |meta| {
            let s: Expression<F> = meta.query_selector(trace_cols.memory_selector);
            // let step = meta.query_advice(trace_cols.step, Rotation::cur());
            let addr = meta.query_advice(trace_cols.read_addr, Rotation::cur());
            let before = meta.query_advice(trace_cols.read_value, Rotation::cur());
            let after = meta.query_advice(trace_cols.read_value, Rotation::cur());
            vec![
                // (step, memory_config.step),
                (addr, memory_config.addr),
                (before, memory_config.value_before),
                (after, memory_config.value_after),
            ]
        });
        
        // Lookup for WRITE operations
        meta.lookup("memory_write", |meta| {
            let s = meta.query_selector(trace_cols.memory_selector);
            // let step = meta.query_advice(trace_cols.step, Rotation::cur());
            let addr = meta.query_advice(trace_cols.write_addr, Rotation::cur());
            let before = meta.query_advice(trace_cols.write_before, Rotation::cur());
            let after = meta.query_advice(trace_cols.write_after, Rotation::cur());
            
            vec![
                // (step, memory_config.step),
                (addr, memory_config.addr),
                (before, memory_config.value_before),
                (after, memory_config.value_after),
            ]
        });
    }
    
    /// Add constraint that steps are sequential and increasing
    pub fn add_step_ordering_constraint(
        &self,
        meta: &mut ConstraintSystem<F>,
        step_col: Column<Advice>,
        selector: Selector,
    ) {
        meta.create_gate("step ordering", |meta| {
            let s = meta.query_selector(selector);
            let current_step = meta.query_advice(step_col, Rotation::cur());
            let next_step = meta.query_advice(step_col, Rotation::next());
            
            // next_step = current_step + 1
            let one = Expression::Constant(F::ONE);
            vec![s * (next_step - current_step - one)]
        });
    }
}