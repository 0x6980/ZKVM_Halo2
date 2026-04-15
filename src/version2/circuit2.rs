use std::marker::PhantomData;
use halo2_proofs::{circuit::*, plonk::*, poly::Rotation};

use ff::{PrimeField};

use crate::version2::vm2::{TraceRow, MemoryAccess};

// ============================================================================
// Circuit Configuration
// ============================================================================
#[derive(Debug, Clone)]
pub struct SubleqConfig { 
    // Instruction columns
    pub pc: Column<Advice>,                 // Program counter
    pub inst_a: Column<Advice>,             // First operand address
    pub inst_b: Column<Advice>,             // Second operand address
    pub inst_c: Column<Advice>,             // Jump target
    pub branch_taken: Column<Advice>,       // Whether branch is taken (0 or 1)
    pub new_pc: Column<Advice>,             // Next PC value

    // Memory columns with timestamp for consistency
    // ===== Memory Access 1: Read A =====
    pub read_a_addr: Column<Advice>,
    pub read_a_value: Column<Advice>,
    pub read_a_timestamp: Column<Advice>,

    // ===== Memory Access 2: Read B =====
    pub read_b_addr: Column<Advice>,
    pub read_b_value: Column<Advice>,
    pub read_b_timestamp: Column<Advice>,

    // ===== Memory Access 3: Write B =====
    pub write_b_addr: Column<Advice>,
    pub write_b_value: Column<Advice>,
    pub write_b_timestamp: Column<Advice>,

    // ===== Validity =====
    pub instruction_selector: Selector,
    
    // Range checks
    pub addr_range: TableColumn,
    pub value_range: TableColumn,
    
    pub instance: Column<Instance>,
}

// ============================================================================
// Circuit Implementation with Permutation
// ============================================================================
#[derive(Default)]
pub struct SubleqCircuit<F: PrimeField> {
    pub initial_memory: Vec<(usize, i64)>,
    pub trace: Vec<TraceRow>,
    pub memory_accesses: Vec<MemoryAccess>,
    pub _marker: PhantomData<F>,
}

impl<F: PrimeField> SubleqCircuit<F> {
    pub fn new(initial_memory: Vec<(usize, i64)>, trace: Vec<TraceRow>, memory_accesses: Vec<MemoryAccess>) -> Self {
        Self { initial_memory, trace, memory_accesses, _marker: PhantomData }
    }
}

impl<F: PrimeField> Circuit<F> for SubleqCircuit<F> {
    type Config = SubleqConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::new(vec![], vec![], vec![])
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        // Create columns
        let pc = meta.advice_column();
        let inst_a = meta.advice_column();
        let inst_b = meta.advice_column();
        let inst_c = meta.advice_column();
        let branch_taken = meta.advice_column();
        let new_pc = meta.advice_column();
        
        let read_a_addr = meta.advice_column();
        let read_a_value = meta.advice_column();
        let read_a_timestamp = meta.advice_column();
        
        let read_b_addr = meta.advice_column();
        let read_b_value = meta.advice_column();
        let read_b_timestamp = meta.advice_column();
        
        let write_b_addr = meta.advice_column();
        let write_b_value = meta.advice_column();
        let write_b_timestamp = meta.advice_column();
        
        let instruction_selector = meta.selector();

        let addr_range = meta.lookup_table_column();
        let value_range = meta.lookup_table_column();
        
        let instance = meta.instance_column();
        
        // ====================================================================
        // CONSTRAINT 1: SUBLEQ Arithmetic
        // ====================================================================
        meta.create_gate("subleq arithmetic", |meta| {
            let s = meta.query_selector(instruction_selector);
            let val_a = meta.query_advice(read_a_value, Rotation::cur());
            let val_b = meta.query_advice(read_b_value, Rotation::cur());
            let result = meta.query_advice(write_b_value, Rotation::cur());
            
            vec![s * (result - (val_b - val_a))]
        });
        
        // ====================================================================
        // CONSTRAINT 2: Address Consistency
        // ====================================================================
        meta.create_gate("address consistency", |meta| {
            let s = meta.query_selector(instruction_selector);
            let a = meta.query_advice(inst_a, Rotation::cur());
            let b = meta.query_advice(inst_b, Rotation::cur());
            let read_a = meta.query_advice(read_a_addr, Rotation::cur());
            let read_b = meta.query_advice(read_b_addr, Rotation::cur());
            let write_b = meta.query_advice(write_b_addr, Rotation::cur());
            
            vec![
                s.clone() * (read_a - a),
                s.clone() * (read_b - b.clone()),
                s * (write_b - b),
            ]
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



        meta.create_gate("conditional_constraint", |meta| {
            let s = meta.query_selector(instruction_selector);
            
            let b_addr_cur = meta.query_advice(read_b_addr, Rotation::cur());
            let write_b_cur = meta.query_advice(write_b_value, Rotation::cur());


            let a_addr_next = meta.query_advice(read_a_addr, Rotation::next());
            let a_value_next = meta.query_advice(read_a_value, Rotation::next());

            let b_addr_next = meta.query_advice(read_b_addr, Rotation::next());
            let b_value_next = meta.query_advice(read_b_value, Rotation::next());

            // Constraint 1: If b_addr_cur == a_addr_next, then b_value_next == write_b_cur
            // Enforced as: (a0 - a1) * (b_value_next - write_b_cur) = 0
            let constraint1 = s.clone() * (b_addr_cur.clone() - a_addr_next) * (a_value_next.clone() - write_b_cur.clone());
            
            // Constraint 2: If b_addr_cur == b_addr_next, then b_value_next == write_b_cur
            let constraint2 = s * (b_addr_cur - b_addr_next) * (b_value_next - write_b_cur);
            
            vec![constraint1, constraint2]
        });
        
        // ====================================================================
        // CONSTRAINT 6: Range Checks
        // ====================================================================
        meta.lookup("address range", |meta| {
            let a_addr = meta.query_advice(read_a_addr, Rotation::cur());
            let b_addr = meta.query_advice(read_b_addr, Rotation::cur());
            vec![
                (a_addr, addr_range),
                (b_addr, addr_range),
            ]
        });
        
        meta.lookup("value range", |meta| {
            let a_value = meta.query_advice(read_a_value, Rotation::cur());
            let b_value = meta.query_advice(read_b_value, Rotation::cur());
            vec![
                (a_value, value_range),
                (b_value, value_range),
                ]
        });
        
        SubleqConfig {
            pc, inst_a, inst_b, inst_c, branch_taken, new_pc,
            read_a_addr, read_a_value, read_a_timestamp,
            read_b_addr, read_b_value, read_b_timestamp,
            write_b_addr, write_b_value, write_b_timestamp,
            instruction_selector,
            addr_range, value_range,
            instance,
        }
    }
    
    fn synthesize(&self, config: Self::Config, mut layouter: impl Layouter<F>) -> Result<(), Error> {
        // Load range tables
        layouter.assign_table(|| "address range", |mut table| {
            for i in 0..256 {
                table.assign_cell(|| format!("addr_{}", i), config.addr_range, i, 
                    || Value::known(F::from(i as u64)))?;
            }
            Ok(())
        })?;
        
        layouter.assign_table(|| "value range", |mut table| {
            for i in 0..65536 {
                table.assign_cell(|| format!("value_{}", i), config.value_range, i, 
                    || Value::known(F::from(i as u64)))?;
            }
            Ok(())
        })?;
        
        // Assign rows with permutation columns
        layouter.assign_region(|| "memory permutation", |mut region| {
            // Assign instruction rows
            for (idx, row) in self.trace.iter().enumerate() {
                config.instruction_selector.enable(&mut region, idx)?;
                
                // Instruction columns
                region.assign_advice(|| "pc", config.pc, idx, || Value::known(F::from(row.pc as u64)))?;
                region.assign_advice(|| "inst_a", config.inst_a, idx, || Value::known(F::from(row.inst_a as u64)))?;
                region.assign_advice(|| "inst_b", config.inst_b, idx, || Value::known(F::from(row.inst_b as u64)))?;
                region.assign_advice(|| "inst_c", config.inst_c, idx, || Value::known(F::from(row.inst_c as u64)))?;
                region.assign_advice(|| "branch_taken", config.branch_taken, idx, || Value::known(F::from(row.branch_taken as u64)))?;
                region.assign_advice(|| "new_pc", config.new_pc, idx, || Value::known(F::from(row.new_pc as u64)))?;
                
                // Memory columns
                region.assign_advice(|| "read_a_addr", config.read_a_addr, idx, || Value::known(F::from(row.inst_a as u64)))?;
                region.assign_advice(|| "read_a_value", config.read_a_value, idx, || Value::known(F::from(row.op_a_value as i64 as u64)))?;
                // region.assign_advice(|| "read_a_timestamp", config.read_a_timestamp, idx, || Value::known(F::from(row.read_a_timestamp as u64)))?;
                
                region.assign_advice(|| "read_b_addr", config.read_b_addr, idx, || Value::known(F::from(row.inst_b as u64)))?;
                region.assign_advice(|| "read_b_value", config.read_b_value, idx, || Value::known(F::from(row.op_b_value as i64 as u64)))?;
                // region.assign_advice(|| "read_b_timestamp", config.read_b_timestamp, idx, || Value::known(F::from(row.read_b_timestamp as u64)))?;
                
                region.assign_advice(|| "write_b_addr", config.write_b_addr, idx, || Value::known(F::from(row.inst_c as u64)))?;
                region.assign_advice(|| "write_b_value", config.write_b_value, idx, || Value::known(F::from(row.op_result as i64 as u64)))?;
                // region.assign_advice(|| "write_b_timestamp", config.write_b_timestamp, idx, || Value::known(F::from(row.write_b_timestamp as u64)))?;
                
            }
            
            // Assign permutation columns (these are separate rows for the permutation argument)
            // We create a separate region for the sorted memory events
            Ok(())
        })?;
        
        Ok(())
    }
}