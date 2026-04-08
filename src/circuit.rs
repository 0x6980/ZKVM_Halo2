use std::marker::PhantomData;
use halo2_proofs::{circuit::*, plonk::*, poly::Rotation};

use ff::{PrimeField};

use crate::vm::{TraceAndMemoryAccessRow, MemoryEventType};

// ============================================================================
// Circuit Configuration
// In this design, each row of SubleqConfig is based on memory access. In the VM, we saw that each instruction creates 3 events of memory access
// (read a, read b, write b). So for each instruction in the VM, we have 3 rows in SubleqConfig. 
// The field op_type represents which type of memory event appears in the SubleqConfig rows.
// In this design, each row represents ONE memory access event:
// Row 0: Read a operation
// Row 1: Read b operation
// Row 2: Write b operation
// So the instruction metadata (pc, inst_a, inst_b, inst_c, branch_taken, new_pc) will be duplicated across 3 consecutive rows.
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

    // ===== Memory access data (specific to this event) =====
    pub mem_addr: Column<Advice>,
    pub mem_value: Column<Advice>,
    pub mem_timestamp: Column<Advice>,

    // ===== Memory Operation Type (for permutation) =====
    pub op_type: Column<Advice>,  // 0=ReadA, 1=ReadB, 2=WriteB

    // ===== Instruction ID to link the 3 rows together =====
    pub inst_id: Column<Advice>,            // Same ID for all 3 rows of an instruction

    // ===== Validity =====
    pub is_valid: Column<Advice>,
    pub memory_access_selector: Selector,

    // ===== PERMUTATION ARGUMENT for Memory Consistency =====
    // We create a permutation between:
    // - Write events (op_type=2)
    // - Read events (op_type=0 or 1)
    // 
    // The permutation ensures that for every read, there exists a
    // write with the same (address, value) and timestamp <= read timestamp
    pub perm_addr: Column<Advice>,
    pub perm_value: Column<Advice>,
    pub perm_timestamp: Column<Advice>,
    pub perm_op_type: Column<Advice>,       // For distinguishing readA/readB/writeB in permutation

    // Memory table columns (for initial state)
    pub memory_table: [TableColumn; 3],
    
    // Range checks
    // pub addr_range: TableColumn,
    // pub value_range: TableColumn,
    
    // pub instance: Column<Instance>,
}

// ============================================================================
// Circuit Implementation with Permutation
// ============================================================================
#[derive(Default)]
pub struct SubleqCircuit<F: PrimeField> {
    pub initial_memory: Vec<(usize, i64)>,
    pub trace_memory_accesses: Vec<TraceAndMemoryAccessRow>,
    pub _marker: PhantomData<F>,
}

impl<F: PrimeField> SubleqCircuit<F> {
    pub fn new(initial_memory: Vec<(usize, i64)>, trace_memory_accesses: Vec<TraceAndMemoryAccessRow>) -> Self {
        Self { initial_memory, trace_memory_accesses, _marker: PhantomData }
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
        let branch_taken = meta.advice_column();
        let new_pc = meta.advice_column();
        
        let mem_addr = meta.advice_column();
        let mem_value = meta.advice_column();
        let mem_timestamp = meta.advice_column();
        
        let op_type = meta.advice_column();
        let inst_id = meta.advice_column();
        let is_valid = meta.advice_column();

        let memory_access_selector = meta.selector();
        
        // Permutation columns
        let perm_addr = meta.advice_column();
        let perm_value = meta.advice_column();
        let perm_timestamp = meta.advice_column();
        let perm_op_type = meta.advice_column();
        
        // Enable equality for permutation columns
        meta.enable_equality(inst_id);
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
        // let addr_range = meta.lookup_table_column();
        // let value_range = meta.lookup_table_column();
        
        // let instance = meta.instance_column();
        

        // ====================================================================
        // CONSTRAINT 1: op_type must be 0, 1, or 2
        // ====================================================================
        meta.create_gate("op_type valid", |meta| {
            let s = meta.query_selector(memory_access_selector);
            let op = meta.query_advice(op_type, Rotation::cur());
            let valid = meta.query_advice(is_valid, Rotation::cur());
            
            // op * (op-1) * (op-2) = 0
            let constraint = op.clone() * (op.clone() - Expression::Constant(F::from(1u64)))
                           * (op.clone() - Expression::Constant(F::from(2u64)));
            
            vec![s * constraint * valid]
        });

        // ====================================================================
        // CONSTRAINT 2: Within same instruction, metadata must be consistent
        // ====================================================================
        meta.create_gate("same instruction metadata", |meta| {
            let s = meta.query_selector(memory_access_selector);

            let valid = meta.query_advice(is_valid, Rotation::cur());
            let prev_valid = meta.query_advice(is_valid, Rotation::prev());
            
            let inst_id_cur = meta.query_advice(inst_id, Rotation::cur());
            let inst_id_prev = meta.query_advice(inst_id, Rotation::prev());
            
            let pc_cur = meta.query_advice(pc, Rotation::cur());
            let pc_prev = meta.query_advice(pc, Rotation::prev());
            
            let inst_a_cur = meta.query_advice(inst_a, Rotation::cur());
            let inst_a_prev = meta.query_advice(inst_a, Rotation::prev());
            
            let inst_b_cur = meta.query_advice(inst_b, Rotation::cur());
            let inst_b_prev = meta.query_advice(inst_b, Rotation::prev());
            
            let inst_c_cur = meta.query_advice(inst_c, Rotation::cur());
            let inst_c_prev = meta.query_advice(inst_c, Rotation::prev());
            
            let same_inst = inst_id_cur - inst_id_prev;
            
            vec![
                s.clone() * valid.clone() * prev_valid.clone() * (pc_cur - pc_prev) * same_inst.clone(),
                s.clone() * valid.clone() * prev_valid.clone() * (inst_a_cur - inst_a_prev) * same_inst.clone(),
                s.clone() * valid.clone() * prev_valid.clone() * (inst_b_cur - inst_b_prev) * same_inst.clone(),
                s  * valid * prev_valid * (inst_c_cur - inst_c_prev) * same_inst,
            ]
        });


        // ====================================================================
        // CONSTRAINT 3: Address consistency with instruction operands
        // ====================================================================
        meta.create_gate("address matches instruction", |meta| {
            let s = meta.query_selector(memory_access_selector);

            let valid = meta.query_advice(is_valid, Rotation::cur());
            
            let op = meta.query_advice(op_type, Rotation::cur());
            let addr = meta.query_advice(mem_addr, Rotation::cur());
            let inst_a_val = meta.query_advice(inst_a, Rotation::cur());
            let inst_b_val = meta.query_advice(inst_b, Rotation::cur());
            
            // For ReadA (op=0): addr must equal inst_a
            let is_read_a = Expression::Constant(F::from(1u64)) - op.clone();
            let addr_check_a = (addr.clone() - inst_a_val) * is_read_a;
            
            // For ReadB (op=1) and WriteB (op=2): addr must equal inst_b
            let is_read_b_or_write = op.clone() * (op.clone() - Expression::Constant(F::from(1u64)));
            let addr_check_b = (addr - inst_b_val) * is_read_b_or_write;
            
            vec![
                s.clone() * addr_check_a * valid.clone(),
                s * addr_check_b * valid,
            ]
        });


        // ====================================================================
        // CONSTRAINT 4: SUBLEQ arithmetic across the 3 rows
        // ====================================================================
        meta.create_gate("subleq arithmetic", |meta| {
            let s = meta.query_selector(memory_access_selector);

            let valid = meta.query_advice(is_valid, Rotation::cur());
            let prev_valid = meta.query_advice(is_valid, Rotation::prev());
            let prev2_valid = meta.query_advice(is_valid, Rotation(-2));
            
            let op_cur = meta.query_advice(op_type, Rotation::cur());
            let inst_id_cur = meta.query_advice(inst_id, Rotation::cur());
            let inst_id_prev = meta.query_advice(inst_id, Rotation::prev());
            let inst_id_prev2 = meta.query_advice(inst_id, Rotation(-2));
            
            let val_cur = meta.query_advice(mem_value, Rotation::cur());
            let val_prev = meta.query_advice(mem_value, Rotation::prev());
            let val_prev2 = meta.query_advice(mem_value, Rotation(-2));
            
            // Check if current is WriteB (op=2)
            let is_write = op_cur - Expression::Constant(F::from(2u64));
            
            // Check same instruction across 3 rows
            let same_inst_prev = inst_id_cur.clone() - inst_id_prev;
            let same_inst_prev2 = inst_id_cur - inst_id_prev2;
            
            // For WriteB: value = ReadB value - ReadA value
            let arithmetic_check = val_cur.clone() - (val_prev.clone() - val_prev2.clone());
            
            vec![
                s * is_write * arithmetic_check * same_inst_prev * same_inst_prev2 
                * valid * prev_valid * prev2_valid
            ]
        });

        // ====================================================================
        // CONSTRAINT 5: Branch tracking (only on WriteB row)
        // ====================================================================
        meta.create_gate("branch tracking", |meta| {
            let s = meta.query_selector(memory_access_selector);

            let valid = meta.query_advice(is_valid, Rotation::cur());
            
            let op = meta.query_advice(op_type, Rotation::cur());
            let is_write = op - Expression::Constant(F::from(2u64));
            
            let branch = meta.query_advice(branch_taken, Rotation::cur());
            let branch_binary = branch.clone() * (Expression::Constant(F::from(1u64)) - branch);
            
            // branch_taken must be 0 or 1 only on WriteB rows
            vec![s * is_write * branch_binary * valid]
        });
        
        // ====================================================================
        // CONSTRAINT 6: PC progression (using next instruction's first row)
        // ====================================================================
        meta.create_gate("pc progression", |meta| {
            let s = meta.query_selector(memory_access_selector);
            
            let valid = meta.query_advice(is_valid, Rotation::cur());
            let prev_valid = meta.query_advice(is_valid, Rotation::prev());
            
            let op_cur = meta.query_advice(op_type, Rotation::cur());
            let op_prev = meta.query_advice(op_type, Rotation::prev());
            
            let inst_id_cur = meta.query_advice(inst_id, Rotation::cur());
            let inst_id_prev = meta.query_advice(inst_id, Rotation::prev());
            
            let pc_cur = meta.query_advice(pc, Rotation::cur());
            let new_pc_prev = meta.query_advice(new_pc, Rotation::prev());
            
            // Current is first row of instruction (op=0) and previous is last row (op=2)
            let is_first = op_cur;
            let prev_is_last = op_prev - Expression::Constant(F::from(2u64));
            let diff_inst = inst_id_cur - inst_id_prev - Expression::Constant(F::from(1u64));
            
            let pc_check = pc_cur - new_pc_prev;
            
            vec![
                s * is_first * prev_is_last * diff_inst * pc_check * valid * prev_valid
            ]
        });
        
        // ====================================================================
        // CONSTRAINT 7: Memory consistency via PERMUTATION
        // ====================================================================
        
        // Copy memory access data to permutation columns
        meta.create_gate("permutation mapping", |meta| {
            let s = meta.query_selector(memory_access_selector);
            
            let valid = meta.query_advice(is_valid, Rotation::cur());
            
            let addr = meta.query_advice(mem_addr, Rotation::cur());
            let value = meta.query_advice(mem_value, Rotation::cur());
            let ts = meta.query_advice(mem_timestamp, Rotation::cur());
            let op = meta.query_advice(op_type, Rotation::cur());
            
            let perm_addr_val = meta.query_advice(perm_addr, Rotation::cur());
            let perm_value_val = meta.query_advice(perm_value, Rotation::cur());
            let perm_ts_val = meta.query_advice(perm_timestamp, Rotation::cur());
            let perm_op_val = meta.query_advice(perm_op_type, Rotation::cur());
            
            vec![
                s.clone() * (perm_addr_val - addr) * valid.clone(),
                s.clone() * (perm_value_val - value) * valid.clone(),
                s.clone() * (perm_ts_val - ts) * valid.clone(),
                s * (perm_op_val - op) * valid,
            ]
        });
        
        // Add writes to memory table
        meta.lookup("writes to memory table", |meta| {
            let valid = meta.query_advice(is_valid, Rotation::cur());
            let op = meta.query_advice(op_type, Rotation::cur());
            let is_write = op - Expression::Constant(F::from(2u64));
            
            let addr = meta.query_advice(perm_addr, Rotation::cur());
            let value = meta.query_advice(perm_value, Rotation::cur());
            let ts = meta.query_advice(perm_timestamp, Rotation::cur());
            
            let condition = is_write * valid;
            
            vec![
                (addr * condition.clone(), memory_table[0]),
                (value * condition.clone(), memory_table[1]),
                (ts * condition, memory_table[2]),
            ]
        });
        
        // Reads must exist in memory table
        meta.lookup("reads from memory table", |meta| {
            let valid = meta.query_advice(is_valid, Rotation::cur());
            let op = meta.query_advice(op_type, Rotation::cur());
            let is_read = Expression::Constant(F::from(1u64)) - (op - Expression::Constant(F::from(2u64)));
            
            let addr = meta.query_advice(perm_addr, Rotation::cur());
            let value = meta.query_advice(perm_value, Rotation::cur());
            let ts = meta.query_advice(perm_timestamp, Rotation::cur());
            
            let condition = is_read * valid;
            
            vec![
                (addr * condition.clone(), memory_table[0]),
                (value * condition.clone(), memory_table[1]),
                (ts * condition, memory_table[2]),
            ]
        });
        
        // ====================================================================
        // CONSTRAINT 8: Range checks
        // ====================================================================
        // meta.lookup("address range", |meta| {
        //     let addr = meta.query_advice(mem_addr, Rotation::cur());
        //     let valid = meta.query_advice(is_valid, Rotation::cur());
        //     vec![(addr * valid, addr_range)]
        // });
        
        // meta.lookup("value range", |meta| {
        //     let value = meta.query_advice(mem_value, Rotation::cur());
        //     let valid = meta.query_advice(is_valid, Rotation::cur());
        //     vec![(value * valid, value_range)]
        // });
        
        // ====================================================================
        // CONSTRAINT 9: Timestamp monotonicity
        // ====================================================================
        meta.create_gate("timestamp increases", |meta| {
            let ts_cur = meta.query_advice(mem_timestamp, Rotation::cur());
            let ts_prev = meta.query_advice(mem_timestamp, Rotation::prev());
            let valid_cur = meta.query_advice(is_valid, Rotation::cur());
            let valid_prev = meta.query_advice(is_valid, Rotation::prev());
            
            vec![
                (ts_cur - ts_prev - Expression::Constant(F::from(1u64))) * valid_cur * valid_prev
            ]
        });
        
        SubleqConfig {
            pc, inst_a, inst_b, inst_c, branch_taken, new_pc,
            mem_addr, mem_value, mem_timestamp,
            op_type, inst_id, is_valid,
            memory_access_selector,
            perm_addr, perm_value, perm_timestamp, perm_op_type,
            memory_table, // addr_range, value_range,
            // instance,
        }
    }
    
    fn synthesize(&self, config: Self::Config, mut layouter: impl Layouter<F>) -> Result<(), Error> {
        // Helper for field conversion
        let to_field = |val: i64| -> F {
            if val >= 0 {
                F::from(val as u64)
            } else {
                -F::from((-val) as u64)
            }
        };
        
        let to_field_usize = |val: usize| -> F {
            F::from(val as u64)
        };
        
        let to_field_bool = |val: bool| -> F {
            F::from(if val { 1 } else { 0 })
        };
        
        // Load range tables
        // layouter.assign_table(|| "address range", |mut table| {
        //     for i in 0..256 {
        //         table.assign_cell(
        //             || format!("addr_{}", i),
        //             config.addr_range,
        //             i,
        //             || Value::known(to_field_usize(i))
        //         )?;
        //     }
        //     Ok(())
        // })?;
        
        // layouter.assign_table(|| "value range", |mut table| {
        //     for i in 0..65536 {
        //         let signed_value = (i as i64) - 32768;
        //         table.assign_cell(
        //             || format!("value_{}", i),
        //             config.value_range,
        //             i,
        //             || Value::known(to_field(signed_value))
        //         )?;
        //     }
        //     Ok(())
        // })?;
        
        // Load memory table with initial state
        layouter.assign_table(|| "memory table", |mut table| {
            let mut idx = 0;
            
            // Initial memory as writes at timestamp 0
            for (addr, value) in &self.initial_memory {
                table.assign_cell(|| "init_addr", config.memory_table[0], idx,
                    || Value::known(to_field_usize(*addr)))?;
                table.assign_cell(|| "init_value", config.memory_table[1], idx,
                    || Value::known(to_field(*value)))?;
                table.assign_cell(|| "init_timestamp", config.memory_table[2], idx,
                    || Value::known(F::ZERO))?;
                idx += 1;
            }
            
            // All write operations from trace
            for row in &self.trace_memory_accesses {
                if row.op_type == MemoryEventType::Write {
                    table.assign_cell(|| "write_addr", config.memory_table[0], idx,
                        || Value::known(to_field_usize(row.mem_addr)))?;
                    table.assign_cell(|| "write_value", config.memory_table[1], idx,
                        || Value::known(to_field(row.mem_value)))?;
                    table.assign_cell(|| "write_timestamp", config.memory_table[2], idx,
                        || Value::known(to_field_usize(row.mem_timestamp)))?;
                    idx += 1;
                }
            }
            Ok(())
        })?;
        
        // Assign memory access rows
        layouter.assign_region(|| "memory accesses", |mut region| {
            config.memory_access_selector.enable(&mut region, 0)?;  // Optional: don't enable selector
            region.assign_advice(|| "is_valid", config.is_valid, 0, || Value::known(F::ZERO))?;

            for (row_offset, row) in self.trace_memory_accesses.iter().enumerate() {
                let idx = row_offset + 1;
                config.memory_access_selector.enable(&mut region, idx)?;
                
                // Instruction metadata
                region.assign_advice(|| "pc", config.pc, idx,
                    || Value::known(to_field_usize(row.pc)))?;
                region.assign_advice(|| "inst_a", config.inst_a, idx,
                    || Value::known(to_field_usize(row.inst_a)))?;
                region.assign_advice(|| "inst_b", config.inst_b, idx,
                    || Value::known(to_field_usize(row.inst_b)))?;
                region.assign_advice(|| "inst_c", config.inst_c, idx,
                    || Value::known(to_field_usize(row.inst_c)))?;
                region.assign_advice(|| "branch_taken", config.branch_taken, idx,
                    || Value::known(to_field_bool(row.branch_taken)))?;
                region.assign_advice(|| "new_pc", config.new_pc, idx,
                    || Value::known(to_field_usize(row.new_pc)))?;
                
                // Memory access data
                region.assign_advice(|| "mem_addr", config.mem_addr, idx,
                    || Value::known(to_field_usize(row.mem_addr)))?;
                region.assign_advice(|| "mem_value", config.mem_value, idx,
                    || Value::known(to_field(row.mem_value)))?;
                region.assign_advice(|| "mem_timestamp", config.mem_timestamp, idx,
                    || Value::known(to_field_usize(row.mem_timestamp)))?;
                
                // Operation type and instruction ID
                region.assign_advice(|| "op_type", config.op_type, idx,
                    || Value::known(to_field_usize(row.op_type as usize)))?;
                region.assign_advice(|| "inst_id", config.inst_id, idx,
                    || Value::known(to_field_usize(row.inst_id)))?;
                region.assign_advice(|| "is_valid", config.is_valid, idx,
                    || Value::known(F::ONE))?;
                
                // Permutation columns (copy same values)
                region.assign_advice(|| "perm_addr", config.perm_addr, idx,
                    || Value::known(to_field_usize(row.mem_addr)))?;
                region.assign_advice(|| "perm_value", config.perm_value, idx,
                    || Value::known(to_field(row.mem_value)))?;
                region.assign_advice(|| "perm_timestamp", config.perm_timestamp, idx,
                    || Value::known(to_field_usize(row.mem_timestamp)))?;
                region.assign_advice(|| "perm_op_type", config.perm_op_type, idx,
                    || Value::known(to_field_usize(row.op_type as usize)))?;
            }
            Ok(())
        })?;
        
        Ok(())
    }
}