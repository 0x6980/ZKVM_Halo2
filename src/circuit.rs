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
    pub memory_access_selector: Selector,  // select all rows of execution trace
    pub read_a_selector: Selector,
    pub read_b_selector: Selector,
    pub write_selector: Selector,
    pub except_last_selector: Selector,   // select all rows except last row of execution trace


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
    pub addr_range: TableColumn,
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
    pub k: u32,
    pub _marker: PhantomData<F>,
}

impl<F: PrimeField> SubleqCircuit<F> {
    pub fn new(initial_memory: Vec<(usize, i64)>, trace_memory_accesses: Vec<TraceAndMemoryAccessRow>, k: u32) -> Self {
        Self { initial_memory, trace_memory_accesses, k, _marker: PhantomData }
    }
}

impl<F: PrimeField> Circuit<F> for SubleqCircuit<F> {
    type Config = SubleqConfig;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::new(vec![], vec![], 0)
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
        let read_a_selector = meta.selector();
        let read_b_selector = meta.selector();
        let write_selector = meta.selector();
        let except_last_selector = meta.selector();

        
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
        let addr_range = meta.lookup_table_column();
        // let value_range = meta.lookup_table_column();
        
        // let instance = meta.instance_column();
        

        // ====================================================================
        // CONSTRAINT 1: op_type must be 0, 1, or 2
        // ====================================================================
        meta.create_gate("op_type valid", |meta| {
            let s = meta.query_selector(memory_access_selector);
            let op = meta.query_advice(op_type, Rotation::cur());
            // let valid = meta.query_advice(is_valid, Rotation::cur());
            
            // op * (op-1) * (op-2) = 0
            let constraint = op.clone() * (op.clone() - Expression::Constant(F::from(1u64)))
                           * (op.clone() - Expression::Constant(F::from(2u64)));
            
            vec![s * constraint]
        });

        // ====================================================================
        // CONSTRAINT 2: Within same instruction, metadata must be consistent (3 rows with same instruction metadata)
        // ====================================================================
        meta.create_gate("same instruction metadata", |meta| {
            let s = meta.query_selector(read_a_selector);

            let inst_id_cur = meta.query_advice(inst_id, Rotation::cur());
            let inst_id_next = meta.query_advice(inst_id, Rotation::next());
            let inst_id_next2 = meta.query_advice(inst_id, Rotation(2));
            
            let pc_cur = meta.query_advice(pc, Rotation::cur());
            let pc_next = meta.query_advice(pc, Rotation::next());
            let pc_next2 = meta.query_advice(pc, Rotation(2));
            
            let inst_a_cur = meta.query_advice(inst_a, Rotation::cur());
            let inst_a_next = meta.query_advice(inst_a, Rotation::next());
            let inst_a_next2 = meta.query_advice(inst_a, Rotation(2));
            
            let inst_b_cur = meta.query_advice(inst_b, Rotation::cur());
            let inst_b_next = meta.query_advice(inst_b, Rotation::next());
            let inst_b_next2 = meta.query_advice(inst_b, Rotation(2));
            
            let inst_c_cur = meta.query_advice(inst_c, Rotation::cur());
            let inst_c_next = meta.query_advice(inst_c, Rotation::next());
            let inst_c_next2 = meta.query_advice(inst_c, Rotation(2));
            
            vec![
                s.clone() * (inst_id_cur - inst_id_next.clone()) * (inst_id_next - inst_id_next2),
                s.clone() * (pc_cur - pc_next.clone()) * (pc_next - pc_next2),
                s.clone() * (inst_a_cur - inst_a_next.clone()) * (inst_a_next - inst_a_next2),
                s.clone() * (inst_b_cur - inst_b_next.clone()) * (inst_b_next - inst_b_next2),
                s * (inst_c_cur - inst_c_next.clone()) * (inst_c_next - inst_c_next2),
            ]
        });


        // ====================================================================
        // CONSTRAINT 3: Address consistency with instruction operands
        // ====================================================================
        // meta.create_gate("address matches instruction", |meta| {
        //     let s = meta.query_selector(memory_access_selector);
            
        //     let op = meta.query_advice(op_type, Rotation::cur());
        //     let addr = meta.query_advice(mem_addr, Rotation::cur());
        //     let inst_a_val = meta.query_advice(inst_a, Rotation::cur());
        //     let inst_b_val = meta.query_advice(inst_b, Rotation::cur());
            
        //     // For ReadA (op=0): addr must equal inst_a
        //     let is_read_a = op.clone() - Expression::Constant(F::from(1u64));
        //     let addr_check_a = (addr.clone() - inst_a_val) * is_read_a;
            
        //     // For ReadB (op=1) and WriteB (op=2): addr must equal inst_b
        //     let is_read_b_or_write = op.clone() * (op.clone() - Expression::Constant(F::from(1u64)));
        //     let addr_check_b = (addr - inst_b_val) * is_read_b_or_write;
            
        //     vec![
        //         s.clone() * addr_check_a,
        //         s * addr_check_b,
        //     ]
        // });

        meta.create_gate("read a address", |meta| {
            let s = meta.query_selector(read_a_selector);
            let addr = meta.query_advice(mem_addr, Rotation::cur());
            let inst_a = meta.query_advice(inst_a, Rotation::cur());
            vec![s * (addr - inst_a)]
        });

        meta.create_gate("read b address", |meta| {
            let s = meta.query_selector(read_b_selector);
            let addr = meta.query_advice(mem_addr, Rotation::cur());
            let inst_b = meta.query_advice(inst_b, Rotation::cur());
            vec![s * (addr - inst_b)]
        });

        meta.create_gate("write address", |meta| {
            let s = meta.query_selector(write_selector);
            let addr = meta.query_advice(mem_addr, Rotation::cur());
            let inst_b = meta.query_advice(inst_b, Rotation::cur());
            vec![s * (addr - inst_b)]
        });


        // ====================================================================
        // CONSTRAINT 4: SUBLEQ arithmetic across the 3 rows
        // ====================================================================
        meta.create_gate("subleq arithmetic", |meta| {
            let s = meta.query_selector(read_a_selector);
            
            let val_cur = meta.query_advice(mem_value, Rotation::cur());
            let val_next = meta.query_advice(mem_value, Rotation::next());
            let val_next2 = meta.query_advice(mem_value, Rotation(2));
            
            // For WriteB: value = ReadB value - ReadA value
            let arithmetic_check = val_cur.clone() - (val_next.clone() - val_next2.clone());
            
            vec![
                s * arithmetic_check
            ]
        });

        // ====================================================================
        // CONSTRAINT 5: Branch tracking (only on WriteB row)
        // ====================================================================
        meta.create_gate("branch tracking", |meta| {
            let s = meta.query_selector(write_selector);
            
            let branch = meta.query_advice(branch_taken, Rotation::cur());
            let branch_binary = branch.clone() * (Expression::Constant(F::from(1u64)) - branch);
            
            // branch_taken must be 0 or 1 only on WriteB rows
            vec![s * branch_binary]
        });
        
        // ====================================================================
        // CONSTRAINT 6: PC progression (using next instruction's first row)
        // ====================================================================
        meta.create_gate("pc progression", |meta| {
            let s = meta.query_selector(read_a_selector);

            let pc_val = meta.query_advice(pc, Rotation::cur());
            let c_val = meta.query_advice(inst_c, Rotation::cur());
            let branch = meta.query_advice(branch_taken, Rotation::cur());
            let new_pc_val = meta.query_advice(new_pc, Rotation::cur());
            
            let pc_plus_3 = pc_val + Expression::Constant(F::from(3u64));
            let expected = pc_plus_3 * (Expression::Constant(F::from(1u64)) - branch.clone()) + c_val * branch;
            
            vec![
                s * (new_pc_val - expected)
            ]
        });
        
        // ====================================================================
        // CONSTRAINT 7: Memory consistency via PERMUTATION
        // ====================================================================
        
        // Copy memory access data to permutation columns
        meta.create_gate("permutation mapping", |meta| {
            let s = meta.query_selector(memory_access_selector);
            
            let addr = meta.query_advice(mem_addr, Rotation::cur());
            let value = meta.query_advice(mem_value, Rotation::cur());
            let ts = meta.query_advice(mem_timestamp, Rotation::cur());
            let op = meta.query_advice(op_type, Rotation::cur());
            
            let perm_addr_val = meta.query_advice(perm_addr, Rotation::cur());
            let perm_value_val = meta.query_advice(perm_value, Rotation::cur());
            let perm_ts_val = meta.query_advice(perm_timestamp, Rotation::cur());
            let perm_op_val = meta.query_advice(perm_op_type, Rotation::cur());
            
            vec![
                s.clone() * (perm_addr_val - addr),
                s.clone() * (perm_value_val - value),
                s.clone() * (perm_ts_val - ts),
                s * (perm_op_val - op),
            ]
        });

        // ====================================================================
        // CONSTRAINT 8: Timestamp monotonicity
        // ====================================================================
        meta.create_gate("timestamp increases", |meta| {
            let s = meta.query_selector(except_last_selector);

            let ts_cur = meta.query_advice(mem_timestamp, Rotation::cur());
            let ts_nex = meta.query_advice(mem_timestamp, Rotation::next());
            // let ts_nex2 = meta.query_advice(mem_timestamp, Rotation(2));
            
            vec![
                s.clone() * (ts_nex.clone() - ts_cur - Expression::Constant(F::from(1u64))),
                // s * (ts_nex2 - ts_nex - Expression::Constant(F::from(1u64)))
            ]
        });

        // ====================================================================
        // CONSTRAINT 9: Range checks
        // ====================================================================
        meta.lookup("address range", |meta| {
            let addr = meta.query_advice(mem_addr, Rotation::cur());
            vec![(addr, addr_range)]
        });
        
        // meta.lookup("value range", |meta| {
        //     let value = meta.query_advice(mem_value, Rotation::cur());
        //     vec![(value, value_range)]
        // });
        

        
        // Add writes to memory table
        meta.lookup("writes to memory table", |meta| {
            let is_valid = meta.query_advice(is_valid, Rotation::cur());
            let op = meta.query_advice(op_type, Rotation::cur());
            // let is_write = Expression::Constant(F::from(2u64)) - op.clone();
            
            let addr = meta.query_advice(perm_addr, Rotation::cur());
            let value = meta.query_advice(perm_value, Rotation::cur());
            let ts = meta.query_advice(perm_timestamp, Rotation::cur());
            
            let condition = Expression::Constant(F::ONE) * is_valid;
            println!("{:?}", "11111111111111111111111111111111111111111111111111111111111111111111111111111");
            println!("{:?}", op.clone());
            println!("{:?}", memory_table[0]);
            println!("{:?}", memory_table[1]);
            println!("{:?}", memory_table[2]);
            println!("{:?}", "11111111111111111111111111111111111111111111111111111111111111111111111111111");

            vec![
                (addr * condition.clone(), memory_table[0]),
                (value * condition.clone(), memory_table[1]),
                (ts * condition, memory_table[2]),
            ]
        });
        
        // Reads must exist in memory table
        // meta.lookup("reads from memory table", |meta| {
        //     let valid = meta.query_advice(is_valid, Rotation::cur());
        //     let op = meta.query_advice(op_type, Rotation::cur());
        //     let is_read = Expression::Constant(F::from(1u64)) - (op - Expression::Constant(F::from(2u64)));
            
        //     let addr = meta.query_advice(perm_addr, Rotation::cur());
        //     let value = meta.query_advice(perm_value, Rotation::cur());
        //     let ts = meta.query_advice(perm_timestamp, Rotation::cur());
            
        //     let condition = is_read * valid;
            
        //     vec![
        //         (addr * condition.clone(), memory_table[0]),
        //         (value * condition.clone(), memory_table[1]),
        //         (ts * condition, memory_table[2]),
        //     ]
        // });
        
        SubleqConfig {
            pc, inst_a, inst_b, inst_c, branch_taken, new_pc,
            mem_addr, mem_value, mem_timestamp,
            op_type, inst_id, is_valid,
            memory_access_selector,
            read_a_selector,
            read_b_selector,
            write_selector,
            except_last_selector,
            perm_addr, perm_value, perm_timestamp, perm_op_type,
            memory_table, addr_range, // value_range,
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
        layouter.assign_table(|| "address range", |mut table| {
            for i in 0..256 {
                table.assign_cell(
                    || format!("addr_{}", i),
                    config.addr_range,
                    i,
                    || Value::known(to_field_usize(i))
                )?;
            }
            Ok(())
        })?;
        
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
            
            // // Initial memory as writes at timestamp 0
            // for (addr, value) in &self.initial_memory {
            //     table.assign_cell(|| "write_addr", config.memory_table[0], idx,
            //         || Value::known(to_field_usize(*addr)))?;
            //     table.assign_cell(|| "write_value", config.memory_table[1], idx,
            //         || Value::known(to_field(*value)))?;
            //     table.assign_cell(|| "write_timestamp", config.memory_table[2], idx,
            //         || Value::known(F::ZERO))?;
            //     idx += 1;
            // }
            
            // All write operations from trace
            for row in &self.trace_memory_accesses {
                if row.op_type == MemoryEventType::Write {
                    println!("{:?}", "!!!!!!!!!!!!!!!!!!!!!!!!!!!!!");
                    println!("{:?}", (row.mem_addr, row.mem_value, row.mem_timestamp));
                    println!("{:?}", idx);
                    println!("{:?}", "!!!!!!!!!!!!!!!!!!!!!!!!!!!!!11");
                    table.assign_cell(|| "write_addr", config.memory_table[0], idx,
                        || Value::known(to_field_usize(1000)))?;
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
            for (idx, row) in self.trace_memory_accesses.iter().enumerate() {
            
                // Enable selectors
                config.memory_access_selector.enable(&mut region, idx)?;
                if row.op_type == MemoryEventType::ReadA {
                    config.read_a_selector.enable(&mut region, idx)?;
                } else if row.op_type == MemoryEventType::ReadB {
                    config.read_b_selector.enable(&mut region, idx)?;
                } else if row.op_type == MemoryEventType::Write {
                    config.write_selector.enable(&mut region, idx)?;
                }

                if idx != self.trace_memory_accesses.len() - 1 {
                    config.except_last_selector.enable(&mut region, idx)?;
                }

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
                
                let mut is_valid = Value::known(F::ONE);
                if idx == 0 {
                   is_valid = Value::known(F::ZERO);
                }

                region.assign_advice(|| "is_valid", config.is_valid, idx,
                    || is_valid)?;
                
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
            
            let num_rows = 1 << self.k;
            for idx in self.trace_memory_accesses.len()..num_rows -2 {
                region.assign_advice(|| "is_valid", config.is_valid, idx, || Value::known(F::ZERO))?;
            }

            Ok(())
        })?;
        
        Ok(())
    }
}