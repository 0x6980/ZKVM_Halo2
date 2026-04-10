1. vm.rs
2. circuit.rs
3. tests.rs

# vm.rs: SUBLEQ Virtual Machine with Execution Tracing

A Rust implementation of a SUBLEQ (Subtract and Branch if Less than or Equal to Zero) virtual machine with comprehensive execution tracing and memory access logging capabilities.

## Overview

SUBLEQ is a one-instruction set computer (OISC) architecture where a single instruction performs subtraction and conditional branching. This implementation provides a VM that executes SUBLEQ programs and generates detailed execution traces including memory access patterns.

## Architecture

### SUBLEQ Instruction

The SUBLEQ instruction follows the format: `SUBLEQ a, b, c`

**Operation:** 
memory[b] = memory[b] - memory[a]
if (memory[b] <= 0) then jump to c



**Instruction Fields:**
- `a`: Source memory address
- `b`: Destination memory address (also used for condition checking)
- `c`: Jump target address (executed if result ≤ 0)

## Core Components

### Data Structures

#### `Instruction`
Represents a single SUBLEQ instruction with three operands.

#### `TraceRow`
Records detailed execution information for each instruction:
- Program counter (PC)
- Instruction operands (a, b, c)
- Values before/after execution
- Branch decision
- Next PC value

#### `TraceAndMemoryAccessRow`
Extended trace record that captures individual memory events:
- Memory address accessed
- Value read/written
- Timestamp of access
- Memory event type (ReadA, ReadB, Write)
- Instruction ID for grouping related memory events

#### `MemoryEventType`
Enum defining the three types of memory operations:
- `ReadA`: Reading from address a
- `ReadB`: Reading from address b (before write)
- `Write`: Writing result to address b

#### `SubleqState`
Maintains VM state including:
- Program counter (PC)
- Fixed-size memory array (256 cells)

## Features

- **Complete Execution Tracing**: Records every step of program execution
- **Memory Access Logging**: Tracks all memory reads and writes with timestamps
- **Memory Consistency**: Maintains proper order of memory operations
- **Configurable Memory Size**: Fixed 256-cell memory for simplicity
- **Step Limit Protection**: Prevents infinite loops with configurable maximum steps


# circuit.ir: SUBLEQ zkVM Circuit using Halo2

A zero-knowledge proof circuit implementation of a SUBLEQ (Subtract and Branch if Less than or Equal to Zero) virtual machine using the Halo2 proving system. This circuit verifies correct execution of SUBLEQ programs with comprehensive memory consistency guarantees.

## Overview

This implementation transforms SUBLEQ execution traces into a zero-knowledge circuit that can be verified efficiently. The circuit proves that a given sequence of memory operations correctly corresponds to valid SUBLEQ program execution, including proper arithmetic operations, branching logic, and memory consistency.

## Circuit Architecture

### Core Design Principle

Each SUBLEQ instruction generates three memory events, and the circuit represents **each memory event as a separate row**:

Instruction N:
- Row 3N: Read A operation (op_type = 0)
- Row 3N+1: Read B operation (op_type = 1)
- Row 3N+2: Write B operation (op_type = 2)


This design allows the circuit to:
- Verify memory consistency across operations
- Enforce correct ordering of reads and writes
- Validate SUBLEQ arithmetic across three rows
- Track program counter progression

## Circuit Components

### Configuration Columns

#### Instruction Metadata (per row)
- `pc`: Program counter value
- `inst_a`, `inst_b`, `inst_c`: SUBLEQ instruction operands
- `branch_taken`: Whether branch condition was met (0/1)
- `new_pc`: Next program counter value

#### Memory Access Data
- `mem_addr`: Memory address accessed
- `mem_value`: Value read from or written to memory
- `mem_timestamp`: Global timestamp for memory operation ordering

#### Operation Tracking
- `op_type`: Memory operation type (0=ReadA, 1=ReadB, 2=Write)
- `inst_id`: Instruction identifier linking related rows
- `is_valid`: Row validity flag (for padding)

#### Permutation Columns (Memory Consistency)
- `perm_addr`, `perm_value`, `perm_timestamp`, `perm_op_type`: Copies of memory access data used for permutation argument

#### Lookup Tables
- `memory_table`: Stores all write operations (3 columns: address, value, timestamp)
- `addr_range`: Range table for address validation (0-255)

### Selectors
- `memory_access_selector`: Enables all trace rows
- `read_a_selector`: Enables ReadA operation rows
- `read_b_selector`: Enables ReadB operation rows
- `write_selector`: Enables Write operation rows
- `except_last_selector`: Enables all rows except last (for monotonicity checks)

## Constraints Implemented

### 1. Valid Operation Type
Ensures `op_type` is 0, 1, or 2:

### 2. Instruction Metadata Consistency
For rows belonging to the same instruction (same `inst_id`), verifies that:
- PC values are identical
- Instruction operands (a, b, c) are identical
- Applies to triples of consecutive rows

### 3. Address Matching
Each operation type must access the correct address:
- **ReadA (op_type=0)**: `mem_addr == inst_a`
- **ReadB (op_type=1)**: `mem_addr == inst_b`
- **Write (op_type=2)**: `mem_addr == inst_b`

### 4. SUBLEQ Arithmetic
Verifies the core SUBLEQ operation across the three rows of an instruction:
Implemented as: `ReadA_value - (ReadB_value - Write_value) = 0`

### 5. Branch Tracking
Ensures `branch_taken` is binary (0 or 1) on Write rows:

branch_taken * (1 - branch_taken) = 0
### 6. Program Counter Progression
Verifies correct PC update based on branch condition:

new_pc = (pc + 3) * (1 - branch_taken) + inst_c * branch_taken

### 7. Memory Consistency via Permutation
Creates a permutation argument between memory access columns and permutation columns, enabling:
- Read-after-write consistency
- Memory initialization verification
- Proper temporal ordering

### 8. Timestamp Monotonicity
Ensures timestamps increase by exactly 1 between consecutive rows:

timestamp_next - timestamp_current = 1

### 9. Address Range Check
Validates all memory addresses are within bounds (0-255) using table lookup.

### 10. Memory Table Lookup
All write operations are added to the memory table for consistency verification.

## Usage
See the tests.ir file.