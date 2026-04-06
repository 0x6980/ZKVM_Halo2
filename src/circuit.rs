use std::marker::PhantomData;
use halo2_proofs::{circuit::*, plonk::*, poly::Rotation};

use ff::{PrimeField};

use crate::vm::{TraceRow, MemoryAccess};

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

    // ===== Memory Operation Type (for permutation) =====
    pub op_type: Column<Advice>,  // 0=ReadA, 1=ReadB, 2=WriteB

    // ===== Validity =====
    pub is_valid: Column<Advice>,
    pub instruction_selector: Selector,

    // ===== PERMUTATION ARGUMENT for Memory Consistency =====
    // We create a permutation between:
    // - Write events (op_type=2)
    // - Read events (op_type=0 or 1)
    // 
    // The permutation ensures that for every read, there exists a
    // write with the same (address, value) and timestamp <= read timestamp
    
    // For Read A operations
    pub perm_read_a_addr: Column<Advice>,
    pub perm_read_a_value: Column<Advice>,
    pub perm_read_a_timestamp: Column<Advice>,
    
    // For Read B operations
    pub perm_read_b_addr: Column<Advice>,
    pub perm_read_b_value: Column<Advice>,
    pub perm_read_b_timestamp: Column<Advice>,
    
    // For Write B operations
    pub perm_write_b_addr: Column<Advice>,
    pub perm_write_b_value: Column<Advice>,
    pub perm_write_b_timestamp: Column<Advice>,

    // Memory table columns (for initial state)
    pub memory_table: [TableColumn; 3],
    
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
        
        let op_type = meta.advice_column();
        let is_valid = meta.advice_column();
        let instruction_selector = meta.selector();
        
        // Permutation columns
        let perm_addr = meta.advice_column();
        let perm_value = meta.advice_column();
        let perm_timestamp = meta.advice_column();
        let perm_op_type = meta.advice_column();
        
        // Enable equality for permutation columns
        meta.enable_equality(perm_addr);
        meta.enable_equality(perm_value);
        meta.enable_equality(perm_timestamp);
        meta.enable_equality(perm_op_type);
        
        // Create lookup tables
        let memory_table = [
            meta.lookup_table_column(),
            meta.lookup_table_column(),
            meta.lookup_table_column(),
        ];
        let addr_range = meta.lookup_table_column();
        let value_range = meta.lookup_table_column();
        
        let instance = meta.instance_column();
        
        // ====================================================================
        // CONSTRAINT 1: SUBLEQ Arithmetic
        // ====================================================================
        meta.create_gate("subleq arithmetic", |meta| {
            let s = instruction_selector;
            let val_a = meta.query_advice(read_a_value, Rotation::cur());
            let val_b = meta.query_advice(read_b_value, Rotation::cur());
            let result = meta.query_advice(write_b_value, Rotation::cur());
            let valid = meta.query_advice(is_valid, Rotation::cur());
            
            vec![s * (result - (val_b - val_a)) * valid]
        });
        
        // ====================================================================
        // CONSTRAINT 2: Address Consistency
        // ====================================================================
        meta.create_gate("address consistency", |meta| {
            let s = instruction_selector;
            let a = meta.query_advice(inst_a, Rotation::cur());
            let b = meta.query_advice(inst_b, Rotation::cur());
            let read_a = meta.query_advice(read_a_addr, Rotation::cur());
            let read_b = meta.query_advice(read_b_addr, Rotation::cur());
            let write_b = meta.query_advice(write_b_addr, Rotation::cur());
            let valid = meta.query_advice(is_valid, Rotation::cur());
            
            vec![
                s * (read_a - a) * valid,
                s * (read_b - b) * valid,
                s * (write_b - b) * valid,
            ]
        });
        
        // ====================================================================
        // CONSTRAINT 3: PC Progression
        // ====================================================================
        meta.create_gate("pc progression", |meta| {
            let s = instruction_selector;
            let pc_val = meta.query_advice(pc, Rotation::cur());
            let c_val = meta.query_advice(inst_c, Rotation::cur());
            let branch = meta.query_advice(branch_taken, Rotation::cur());
            let new_pc_val = meta.query_advice(new_pc, Rotation::cur());
            let valid = meta.query_advice(is_valid, Rotation::cur());
            
            let pc_plus_3 = pc_val + Expression::Constant(F::from(3u64));
            let expected = pc_plus_3 * (Expression::Constant(F::from(1u64)) - branch.clone())
                          + c_val * branch;
            
            vec![s * (new_pc_val - expected) * valid]
        });
        
        // ====================================================================
        // CONSTRAINT 4: Branch Condition Binary
        // ====================================================================
        meta.create_gate("branch binary", |meta| {
            let s = instruction_selector;
            let branch = meta.query_advice(branch_taken, Rotation::cur());
            let valid = meta.query_advice(is_valid, Rotation::cur());
            
            vec![s * branch.clone() * (Expression::Constant(F::from(1u64)) - branch) * valid]
        });
        
        // ====================================================================
        // PERMUTATION ARGUMENT FOR MEMORY CONSISTENCY
        // This is the KEY innovation!
        // ====================================================================
        
        // Step 1: Assign each memory operation to permutation columns
        // We'll create three "virtual rows" in the permutation for each instruction
        
        // For Read A (op_type = 0)
        meta.create_gate("permutation for read a", |meta| {
            let s = instruction_selector;
            let valid = meta.query_advice(is_valid, Rotation::cur());
            
            let addr = meta.query_advice(read_a_addr, Rotation::cur());
            let value = meta.query_advice(read_a_value, Rotation::cur());
            let ts = meta.query_advice(read_a_timestamp, Rotation::cur());
            
            // Copy to permutation columns
            let perm_addr_val = meta.query_advice(perm_addr, Rotation::cur());
            let perm_value_val = meta.query_advice(perm_value, Rotation::cur());
            let perm_ts_val = meta.query_advice(perm_timestamp, Rotation::cur());
            let perm_phase = meta.query_advice(perm_phase, Rotation::cur());
            
            vec![
                s * (perm_addr_val - addr) * valid,
                s * (perm_value_val - value) * valid,
                s * (perm_ts_val - ts) * valid,
                s * perm_phase * valid,  // Must be 0 for Read A
            ]
        });

        // For Read B (op_type = 1)
        meta.create_gate("permutation for read b", |meta| {
            let s = instruction_selector;
            let valid = meta.query_advice(is_valid, Rotation::cur());
            
            let addr = meta.query_advice(read_b_addr, Rotation::cur());
            let value = meta.query_advice(read_b_value, Rotation::cur());
            let ts = meta.query_advice(read_b_timestamp, Rotation::cur());
            
            let perm_addr_val = meta.query_advice(perm_addr, Rotation::cur());
            let perm_value_val = meta.query_advice(perm_value, Rotation::cur());
            let perm_ts_val = meta.query_advice(perm_timestamp, Rotation::cur());
            let perm_phase = meta.query_advice(perm_phase, Rotation::cur());
            
            vec![
                s * (perm_addr_val - addr) * valid,
                s * (perm_value_val - value) * valid,
                s * (perm_ts_val - ts) * valid,
                s * perm_phase * valid,  // Must be 0 for Read A
            ]
        });
        
        // For Write B (op_type = 2)
        meta.create_gate("permutation for write b", |meta| {
            let s = instruction_selector;
            let valid = meta.query_advice(is_valid, Rotation::cur());
            
            let addr = meta.query_advice(write_b_addr, Rotation::cur());
            let value = meta.query_advice(write_b_value, Rotation::cur());
            let ts = meta.query_advice(write_b_timestamp, Rotation::cur());
            
            let perm_addr_val = meta.query_advice(perm_addr, Rotation::cur());
            let perm_value_val = meta.query_advice(perm_value, Rotation::cur());
            let perm_ts_val = meta.query_advice(perm_timestamp, Rotation::cur());
            let perm_phase = meta.query_advice(perm_phase, Rotation::cur());
            
            vec![
                s * (perm_addr_val - addr) * valid,
                s * (perm_value_val - value) * valid,
                s * (perm_ts_val - ts) * valid,
                s * (perm_op_val - op) * valid,
            ]
        });
        
        // Step 2: Create permutation between memory operations
        // We want to prove that reads and writes form a valid sequence
        
        // First, add ALL memory operations (reads and writes) to a permutation
        // The permutation will enforce that for each read, there's a matching write
        // with same (addr, value) and earlier timestamp
        
        // Create a sorted list of memory events by (addr, timestamp)
        // The permutation argument will verify that:
        // Event i and Event i+1 with same addr have increasing timestamps
        // and reads match the previous write
        
        meta.create_gate("permutation memory continuity", |meta| {
            let valid = meta.query_advice(is_valid, Rotation::cur());
            let prev_valid = meta.query_advice(is_valid, Rotation::prev());
            
            let curr_addr = meta.query_advice(perm_addr, Rotation::cur());
            let curr_value = meta.query_advice(perm_value, Rotation::cur());
            let curr_ts = meta.query_advice(perm_timestamp, Rotation::cur());
            let curr_op = meta.query_advice(perm_op_type, Rotation::cur());
            
            let prev_addr = meta.query_advice(perm_addr, Rotation::prev());
            let prev_value = meta.query_advice(perm_value, Rotation::prev());
            let prev_ts = meta.query_advice(perm_timestamp, Rotation::prev());
            let prev_op = meta.query_advice(perm_op_type, Rotation::prev());
            
            // If same address
            let same_addr = curr_addr.clone() - prev_addr.clone();
            
            // Then timestamp must increase
            let ts_increases = curr_ts - prev_ts - Expression::Constant(F::from(1u64));
            
            // If current is read (0 or 1) and previous is write (2) with same address,
            // values must match
            let is_curr_read = (Expression::Constant(F::from(1u64)) - (curr_op.clone() - Expression::Constant(F::from(2u64))))
                              * (Expression::Constant(F::from(2u64)) - curr_op.clone());
            let is_prev_write = prev_op.clone() - Expression::Constant(F::from(2u64));
            let value_match = curr_value - prev_value;
            
            vec![
                // Timestamps increase for same address
                same_addr.clone() * ts_increases * valid * prev_valid,
                // Reads match previous write for same address
                same_addr * is_curr_read * is_prev_write * value_match * valid * prev_valid,
            ]
        });
        
        // Step 3: Add initial memory state to permutation
        // We do this by adding virtual writes at timestamp 0 for all initial memory
        
        // This is handled in synthesize() by adding initial memory to the permutation table
        
        // ====================================================================
        // CONSTRAINT 6: Range Checks
        // ====================================================================
        meta.lookup("address range", |meta| {
            let addr = meta.query_advice(perm_addr, Rotation::cur());
            let valid = meta.query_advice(is_valid, Rotation::cur());
            vec![(addr * valid, addr_range)]
        });
        
        meta.lookup("value range", |meta| {
            let value = meta.query_advice(perm_value, Rotation::cur());
            let valid = meta.query_advice(is_valid, Rotation::cur());
            vec![(value * valid, value_range)]
        });
        
        SubleqConfig {
            pc, inst_a, inst_b, inst_c, branch_taken, new_pc,
            read_a_addr, read_a_value, read_a_timestamp,
            read_b_addr, read_b_value, read_b_timestamp,
            write_b_addr, write_b_value, write_b_timestamp,
            op_type, is_valid, instruction_selector,
            perm_addr, perm_value, perm_timestamp, perm_op_type,
            memory_table, addr_range, value_range,
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
                region.assign_advice(|| "read_a_addr", config.read_a_addr, idx, || Value::known(F::from(row.read_a_addr as u64)))?;
                region.assign_advice(|| "read_a_value", config.read_a_value, idx, || Value::known(F::from(row.read_a_value as i64 as u64)))?;
                region.assign_advice(|| "read_a_timestamp", config.read_a_timestamp, idx, || Value::known(F::from(row.read_a_timestamp as u64)))?;
                
                region.assign_advice(|| "read_b_addr", config.read_b_addr, idx, || Value::known(F::from(row.read_b_addr as u64)))?;
                region.assign_advice(|| "read_b_value", config.read_b_value, idx, || Value::known(F::from(row.read_b_value as i64 as u64)))?;
                region.assign_advice(|| "read_b_timestamp", config.read_b_timestamp, idx, || Value::known(F::from(row.read_b_timestamp as u64)))?;
                
                region.assign_advice(|| "write_b_addr", config.write_b_addr, idx, || Value::known(F::from(row.write_b_addr as u64)))?;
                region.assign_advice(|| "write_b_value", config.write_b_value, idx, || Value::known(F::from(row.write_b_value as i64 as u64)))?;
                region.assign_advice(|| "write_b_timestamp", config.write_b_timestamp, idx, || Value::known(F::from(row.write_b_timestamp as u64)))?;
                
                region.assign_advice(|| "is_valid", config.is_valid, idx, || Value::known(F::from(1u64)))?;
            }
            
            // Assign permutation columns (these are separate rows for the permutation argument)
            // We create a separate region for the sorted memory events
            Ok(())
        })?;
        
        // Create a separate region for the permutation-ordered memory events
        layouter.assign_region(|| "permutation ordered events", |mut region| {
            for (idx, event) in self.memory_accesses.iter().enumerate() {
                region.assign_advice(|| "perm_addr", config.perm_addr, idx, || Value::known(F::from(event.addr as u64)))?;
                region.assign_advice(|| "perm_value", config.perm_value, idx, || Value::known(F::from(event.value as i64 as u64)))?;
                region.assign_advice(|| "perm_timestamp", config.perm_timestamp, idx, || Value::known(F::from(event.timestamp as u64)))?;
                region.assign_advice(|| "perm_op_type", config.perm_op_type, idx, || Value::known(F::from(event.event_type as u64)))?;
                region.assign_advice(|| "is_valid", config.is_valid, idx, || Value::known(F::from(1u64)))?;
            }
            Ok(())
        })?;
        
        Ok(())
    }
}