

fn main() {
    println!("Hello, world!");

}

#[cfg(test)]
mod tests {

    use halo2_proofs::dev::MockProver;
    use halo2_proofs::halo2curves::bn256::Fr as Fp;
    use crate::ZKVM;

    #[test]
    fn test_arbitrary_subleq_program() {
        // Example 1: Simple subtraction
        let mut vm = ZKVM::new(256, 100);
        
        // Program: mem[1] = mem[1] - mem[0]; if result <= 0 jump to halt
        let code = vec![
            SubleqInst { a: 0, b: 1, c: 3 },  // Main instruction
            SubleqInst { a: 0, b: 0, c: 0 },  // Halt
        ];
        
        // Initial memory: mem[0] = 10, mem[1] = 5
        let initial_memory = vec![
            Fp::from(10),  // address 0
            Fp::from(5),   // address 1
            Fp::from(0),   // address 2
            Fp::from(0),   // address 3 (code continues)
        ];
        
        vm.load_program(code, initial_memory);
        vm.execute(10).unwrap();
        
        // Verify the ZKVM circuit
        let circuit = vm;
        let public_inputs = vec![
            Fp::from(10),  // initial mem[0]
            Fp::from(5),   // initial mem[1]
            Fp::from(-5),  // final mem[1]
        ];
        
        let prover = MockProver::run(8, &circuit, vec![public_inputs]).unwrap();
        prover.assert_satisfied();
    }
}