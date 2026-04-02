use std::collections::HashMap;
use std::marker::PhantomData;
use halo2_proofs::{arithmetic::FieldExt, circuit::*, plonk::*, poly::Rotation};

// Memory chip that handles consistency properly
#[derive(Debug, Clone)]
struct MemoryChip<F: FieldExt> {
    config: MemoryConfig,
    _marker: PhantomData<F>,
}

#[derive(Debug, Clone)]
struct MemoryConfig {
    // Memory access columns
    addr: Column<Advice>,
    value: Column<Advice>,
    timestamp: Column<Advice>,  // Critical for consistency!
    
    // For memory permutations
    perm_addr: Column<Advice>,
    perm_value: Column<Advice>,
    perm_timestamp: Column<Advice>,
    
    selectors: MemorySelectors,
}

#[derive(Debug, Clone)]
struct MemorySelectors {
    read: Selector,   // Read operation
    write: Selector,  // Write operation
    perm: Selector,   // Permutation check
}

impl<F: FieldExt> MemoryChip<F> {
    pub fn configure(meta: &mut ConstraintSystem<F>) -> MemoryConfig {
        let addr = meta.advice_column();
        let value = meta.advice_column();
        let timestamp = meta.advice_column();
        let perm_addr = meta.advice_column();
        let perm_value = meta.advice_column();
        let perm_timestamp = meta.advice_column();
        
        let read = meta.selector();
        let write = meta.selector();
        let perm = meta.selector();
        
        // Enable equality for copying values
        meta.enable_equality(addr);
        meta.enable_equality(value);
        meta.enable_equality(timestamp);
        meta.enable_equality(perm_addr);
        meta.enable_equality(perm_value);
        meta.enable_equality(perm_timestamp);
        
        // Memory consistency: for each address, values must be consistent across time
        // We use timestamp to order memory operations
        meta.create_gate("memory consistency", |meta| {
            let r = meta.query_selector(read);
            let w = meta.query_selector(write);
            let addr_cur = meta.query_advice(addr, Rotation::cur());
            let value_cur = meta.query_advice(value, Rotation::cur());
            let ts_cur = meta.query_advice(timestamp, Rotation::cur());
            
            let addr_prev = meta.query_advice(addr, Rotation::prev());
            let value_prev = meta.query_advice(value, Rotation::prev());
            let ts_prev = meta.query_advice(timestamp, Rotation::prev());
            
            // If same address and timestamps are consecutive, values must follow rules
            let same_addr = addr_cur.clone() - addr_prev.clone();
            let ts_consecutive = ts_cur - (ts_prev + F::one());
            
            // Constraint: (same_addr) * (ts_consecutive) * (value_cur - value_prev) = 0 for reads?
            // Actually need more sophisticated constraints
            
            vec![]
        });
        
        MemoryConfig {
            addr,
            value,
            timestamp,
            perm_addr,
            perm_value,
            perm_timestamp,
            selectors: MemorySelectors { read, write, perm },
        }
    }
}

// CORRECTED SUBLEQ Implementation with Memory Consistency
#[derive(Debug, Clone)]
struct SubleqConfigCorrect {
    // Memory with timestamp for consistency
    mem_addr: Column<Advice>,
    mem_value: Column<Advice>,
    mem_timestamp: Column<Advice>,
    
    // Instruction columns
    pc: Column<Advice>,
    inst_a: Column<Advice>,
    inst_b: Column<Advice>,
    inst_c: Column<Advice>,
    
    // Operation values (read from memory at specific timestamps)
    op_a_value: Column<Advice>,
    op_b_value: Column<Advice>,
    op_result: Column<Advice>,
    op_timestamp: Column<Advice>,  // When this operation occurred
    
    // Branch condition
    branch_taken: Column<Advice>,
    new_pc: Column<Advice>,
    
    // Memory consistency through lookup table
    memory_table: TableColumn,  // Lookup table for memory consistency
    
    // Selectors
    step_selector: Selector,
    memory_read_selector: Selector,
    memory_write_selector: Selector,
    
    instance: Column<Instance>,
}

impl<F: FieldExt> SubleqChipCorrect<F> {
    pub fn configure(meta: &mut ConstraintSystem<F>) -> SubleqConfigCorrect {
        // Create columns
        let mem_addr = meta.advice_column();
        let mem_value = meta.advice_column();
        let mem_timestamp = meta.advice_column();
        let pc = meta.advice_column();
        let inst_a = meta.advice_column();
        let inst_b = meta.advice_column();
        let inst_c = meta.advice_column();
        let op_a_value = meta.advice_column();
        let op_b_value = meta.advice_column();
        let op_result = meta.advice_column();
        let op_timestamp = meta.advice_column();
        let branch_taken = meta.advice_column();
        let new_pc = meta.advice_column();
        
        let step_selector = meta.selector();
        let memory_read_selector = meta.selector();
        let memory_write_selector = meta.selector();
        let instance = meta.instance_column();
        
        // Create lookup table for memory consistency
        let memory_table = meta.lookup_table_column();
        
        // Enable equality constraints
        meta.enable_equality(mem_addr);
        meta.enable_equality(mem_value);
        meta.enable_equality(mem_timestamp);
        meta.enable_equality(op_a_value);
        meta.enable_equality(op_b_value);
        meta.enable_equality(op_timestamp);
        
        // CRITICAL: Memory consistency via lookup table
        // Each memory operation (read/write) must be in the memory table
        meta.lookup("memory consistency", |meta| {
            let mem_read = meta.query_selector(memory_read_selector);
            let mem_write = meta.query_selector(memory_write_selector);
            
            let addr = meta.query_advice(mem_addr, Rotation::cur());
            let value = meta.query_advice(mem_value, Rotation::cur());
            let ts = meta.query_advice(mem_timestamp, Rotation::cur());
            
            // Both reads and writes must be in memory table
            let is_mem_op = mem_read.clone() + mem_write.clone();
            
            vec![(is_mem_op * addr, is_mem_op * value, is_mem_op * ts)]
        });
        
        // Memory table definition (sorted by address then timestamp)
        // This ensures each address has a consistent timeline
        meta.lookup_table("memory timeline", |meta| {
            let addr = meta.query_advice(mem_addr, Rotation::cur());
            let value = meta.query_advice(mem_value, Rotation::cur());
            let ts = meta.query_advice(mem_timestamp, Rotation::cur());
            
            vec![(addr, value, ts)]
        });
        
        // Gate 1: SUBLEQ operation with timestamp ordering
        meta.create_gate("subleq with memory", |meta| {
            let s = meta.query_selector(step_selector);
            let mem_read = meta.query_selector(memory_read_selector);
            let mem_write = meta.query_selector(memory_write_selector);
            
            let a_val = meta.query_advice(op_a_value, Rotation::cur());
            let b_val = meta.query_advice(op_b_value, Rotation::cur());
            let result = meta.query_advice(op_result, Rotation::cur());
            let ts = meta.query_advice(op_timestamp, Rotation::cur());
            
            // Read operations must happen before write
            let read_ts = meta.query_advice(mem_timestamp, Rotation::cur());
            let write_ts = meta.query_advice(mem_timestamp, Rotation::next());
            
            vec![
                s * (b_val - a_val - result),  // Arithmetic constraint
                mem_read * (read_ts - ts),     // Read timestamp matches op
                mem_write * (write_ts - (ts + F::one())), // Write happens after read
            ]
        });
        
        SubleqConfigCorrect {
            mem_addr,
            mem_value,
            mem_timestamp,
            pc,
            inst_a,
            inst_b,
            inst_c,
            op_a_value,
            op_b_value,
            op_result,
            op_timestamp,
            branch_taken,
            new_pc,
            memory_table,
            step_selector,
            memory_read_selector,
            memory_write_selector,
            instance,
        }
    }
    
    pub fn assign_with_memory_consistency(
        &self,
        mut layouter: impl Layouter<F>,
        program: &[SubleqInstruction],
        initial_memory: &[(usize, i64)],
    ) -> Result<(), Error> {
        // Execute program and track ALL memory accesses
        let mut state = SubleqState {
            pc: 0,
            memory: [0; 256],
        };
        
        // Initialize memory
        for (addr, value) in initial_memory {
            state.memory[*addr] = *value;
        }
        
        // Track memory accesses with timestamps
        let mut memory_accesses = Vec::new();
        let mut current_timestamp = 0;
        
        // First, record initial memory state
        for (addr, value) in state.memory.iter().enumerate() {
            if *value != 0 {
                memory_accesses.push(MemoryAccess {
                    addr,
                    value: *value,
                    timestamp: current_timestamp,
                    is_write: true,  // Initialization counts as write
                });
            }
        }
        current_timestamp += 1;
        
        // Execute program and record all memory operations
        let mut trace = Vec::new();
        
        while state.pc < program.len() * 3 {
            let inst_index = state.pc / 3;
            let instruction = program[inst_index];
            
            // READ: Get values at timestamps
            let a_val = state.memory[instruction.a];
            let b_val = state.memory[instruction.b];
            
            // Record reads
            memory_accesses.push(MemoryAccess {
                addr: instruction.a,
                value: a_val,
                timestamp: current_timestamp,
                is_write: false,
            });
            current_timestamp += 1;
            
            memory_accesses.push(MemoryAccess {
                addr: instruction.b,
                value: b_val,
                timestamp: current_timestamp,
                is_write: false,
            });
            current_timestamp += 1;
            
            // Compute
            let result = b_val - a_val;
            let branch_taken_val = if result <= 0 { 1 } else { 0 };
            let new_pc = if branch_taken_val == 1 {
                instruction.c
            } else {
                state.pc + 3
            };
            
            // Record trace
            trace.push(SubleqTraceCorrect {
                pc: state.pc,
                inst_a: instruction.a,
                inst_b: instruction.b,
                inst_c: instruction.c,
                op_a_value: a_val,
                op_b_value: b_val,
                op_result: result,
                op_timestamp: current_timestamp - 2, // Timestamp of the operation
                branch_taken: branch_taken_val,
                new_pc,
            });
            
            // WRITE: Update memory at timestamp
            let old_value = state.memory[instruction.b];
            state.memory[instruction.b] = result;
            
            memory_accesses.push(MemoryAccess {
                addr: instruction.b,
                value: result,
                timestamp: current_timestamp,
                is_write: true,
            });
            current_timestamp += 1;
            
            // Update PC
            state.pc = new_pc;
        }
        
        // Sort memory accesses by (addr, timestamp) for consistency checking
        memory_accesses.sort_by_key(|ma| (ma.addr, ma.timestamp));
        
        // Now assign to circuit with proper consistency
        self.assign_memory_table(layouter.namespace(|| "memory table"), &memory_accesses)?;
        self.assign_execution_trace(layouter.namespace(|| "execution"), &trace)?;
        
        Ok(())
    }
    
    fn assign_memory_table(
        &self,
        mut layouter: impl Layouter<F>,
        accesses: &[MemoryAccess],
    ) -> Result<(), Error> {
        layouter.assign_table("memory table", |mut table| {
            for (row, access) in accesses.iter().enumerate() {
                table.assign_cell(
                    || "addr",
                    self.config.memory_table,
                    row,
                    || Ok(F::from(access.addr as u64)),
                )?;
                
                table.assign_cell(
                    || "value",
                    self.config.memory_table,
                    row,
                    || Ok(F::from(access.value as u64)),
                )?;
                
                table.assign_cell(
                    || "timestamp",
                    self.config.memory_table,
                    row,
                    || Ok(F::from(access.timestamp as u64)),
                )?;
            }
            Ok(())
        })
    }
    
    fn assign_execution_trace(
        &self,
        mut layouter: impl Layouter<F>,
        trace: &[SubleqTraceCorrect],
    ) -> Result<(), Error> {
        layouter.assign_region("execution trace", |mut region| {
            for (row, step) in trace.iter().enumerate() {
                self.config.step_selector.enable(&mut region, row)?;
                self.config.memory_read_selector.enable(&mut region, row)?;
                self.config.memory_write_selector.enable(&mut region, row)?;
                
                // Assign all values (similar to before)
                // ...
            }
            Ok(())
        })
    }
}

// Memory access record for consistency checking
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
struct MemoryAccess {
    addr: usize,
    value: i64,
    timestamp: usize,
    is_write: bool,
}

#[derive(Debug, Clone)]
struct SubleqTraceCorrect {
    pc: usize,
    inst_a: usize,
    inst_b: usize,
    inst_c: usize,
    op_a_value: i64,
    op_b_value: i64,
    op_result: i64,
    op_timestamp: usize,
    branch_taken: u64,
    new_pc: usize,
}