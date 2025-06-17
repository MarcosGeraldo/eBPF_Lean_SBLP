import «EBPFSpec».Methods

def execMsb (msb : Msb) (x' y' bits : ℕ ) : ℕ  :=
  let x := bitTrim x' bits
  let y := bitTrim y' bits
  let returnVal :=
    match msb with
    | Msb.bpf_add => x + y
    | Msb.bpf_sub => if x < y then x + (makeSigned y bits) else x - y
    | Msb.bpf_mul => x * y
    | Msb.bpf_div => x / y
    | Msb.bpf_sdiv => signedDivision x y bits
    | Msb.bpf_mov => y
    | Msb.bpf_movsx1632 => movsx y 16 32
    | Msb.bpf_movsx1664 => movsx y 16 64
    | Msb.bpf_movsx3264 => movsx y 32 64
    | Msb.bpf_movsx832 => movsx y 8 32
    | Msb.bpf_movsx864 => movsx y 8 64
    | Msb.bpf_mod => x % y
    | Msb.bpf_smod => signedMod x y bits
    | Msb.bpf_neg => negCast x bits
    | Msb.bpf_and => andLogical x y
    | Msb.bpf_or => orLogical x y
    | Msb.bpf_lsh => leftShift x y bits
    | Msb.bpf_rsh => rightShift x y bits
    | Msb.bpf_arsh => assignedRightShift x y bits
    | Msb.bpf_xor => xorLogical x y
    | Msb.bpf_be16 => byteSwapInstructionBe x 4
    | Msb.bpf_be32 => byteSwapInstructionBe x 8
    | Msb.bpf_be64 => byteSwapInstructionBe x 16
    | Msb.bpf_le16 => byteSwapInstructionLe x 4
    | Msb.bpf_le32 => byteSwapInstructionLe x 8
    | Msb.bpf_le64 => byteSwapInstructionLe x 16
    | Msb.bpf_swap16 => byteSwapInstructionSwap x 4
    | Msb.bpf_swap32 => byteSwapInstructionSwap x 8
    | Msb.bpf_swap64 => byteSwapInstructionSwap x 16
    | _ => 0
  bitTrim returnVal bits

def applyWordAlu (regs : Registers) (word : Word) (bits : ℕ ) : Registers :=
  match word with
  | Word.mk imm _offset srcReg destReg opCode =>
    match opCode with
        | OpCode.Eof => regs
        | OpCode.mk msb source _lsb =>
          match msb with
          | Msb.bpf_end => regs
          | _ =>
            match imm with
            | Immediate.mk immVal =>
              let sourceOperand := if source = Source.bpf_k then immVal else readReg regs (getSrcCode srcReg)
              (writeReg regs (getDestCode destReg) (bitTrim (execMsb msb (readReg regs (getDestCode destReg)) sourceOperand bits) bits))
            | Immediate.mkN immVal =>
              let sourceOperand := if source = Source.bpf_k then immVal else readReg regs (getSrcCode srcReg)
              (writeReg regs (getDestCode destReg) (bitTrim (execMsb msb (readReg regs (getDestCode destReg)) (makeSigned sourceOperand bits) bits) bits))

def applyWordMemoryLD (regs : Registers)(stack : MemorySpace) (word : Word) : Registers :=
  returnMemoryBlock regs stack word

def applyWordMemoryST (regs : Registers)(stack : MemorySpace) (word : Word) : MemorySpace :=
  match word with
  | Word.mk imm offsetInput srcReg destReg opCode =>
      match opCode with
        |OpCode.Eof => stack
        |OpCode.mk msb source lsb =>
        let sourceOperand := if lsb = Lsb.bpf_st then (getNatImm imm) else readReg regs (getSrcCode srcReg)
        let indexSrc := if source = Source.bpf_k then 0 else readReg regs (getDestCode destReg)
        let offsetVal := getNatOffset offsetInput indexSrc
        match msb with
          | Msb.bpf_stw => writeMemoryBlock stack offsetVal (natToNatList sourceOperand) 3
          | Msb.bpf_sth => writeMemoryBlock stack offsetVal (natToNatList sourceOperand) 1
          | Msb.bpf_stb => writeMemoryBlock stack offsetVal (natToNatList sourceOperand) 0
          | Msb.bpf_stdw => writeMemoryBlock stack offsetVal (natToNatList sourceOperand) 7
          | Msb.bpf_stxw => writeMemoryBlock stack offsetVal (natToNatList sourceOperand) 3
          | Msb.bpf_stxh => writeMemoryBlock stack offsetVal (natToNatList sourceOperand) 1
          | Msb.bpf_stxb => writeMemoryBlock stack offsetVal (natToNatList sourceOperand) 0
          | Msb.bpf_stxdw => writeMemoryBlock stack offsetVal (natToNatList sourceOperand) 7
          | _ => stack

def applyWordMemorySTX (regs : Registers)(stack : MemorySpace) (word : Word) : MemorySpace :=
  match word with
  | Word.mk imm offsetInput srcReg destReg opCode =>
     match opCode with
        |OpCode.Eof => stack
        |OpCode.mk msb source _lsb =>
        let sourceOperand := if source = Source.bpf_k then (getNatImm imm) else readReg regs (getSrcCode srcReg)
        let indexSrc := if source = Source.bpf_k then 0 else readReg regs (getDestCode destReg)
        let offsetVal := getNatOffset offsetInput indexSrc
        match msb with
          | Msb.bpf_stw => writeMemoryBlock stack offsetVal (natToNatList sourceOperand) 3
          | Msb.bpf_sth => writeMemoryBlock stack offsetVal (natToNatList sourceOperand) 1
          | Msb.bpf_stb => writeMemoryBlock stack offsetVal (natToNatList sourceOperand) 0
          | Msb.bpf_stdw => writeMemoryBlock stack offsetVal (natToNatList sourceOperand) 7
          | Msb.bpf_stxw => writeMemoryBlock stack offsetVal (natToNatList sourceOperand) 3
          | Msb.bpf_stxh => writeMemoryBlock stack offsetVal (natToNatList sourceOperand) 1
          | Msb.bpf_stxb => writeMemoryBlock stack offsetVal (natToNatList sourceOperand) 0
          | Msb.bpf_stxdw => writeMemoryBlock stack offsetVal (natToNatList sourceOperand) 7
          | _ => stack

def evalJmpCond (regs : Registers) (word : Word) (bits : ℕ ) : Bool :=
  match word with
    | Word.mk imm _offset srcReg destReg opCode =>
    match opCode with
      |OpCode.Eof => false
      |OpCode.mk msb source _lsb =>
        match msb with
        | Msb.bpf_ja => true
        | _ =>
        let sourceOperand := if source = Source.bpf_k then (getNatImm imm) else readReg regs (getSrcCode srcReg)
        let sourceOperandTrimmed := bitTrim sourceOperand bits
        let destinationOperand := bitTrim (readReg regs (getDestCode destReg)) bits
        let sourceOperandTrimmed' := evalSigned sourceOperandTrimmed bits
        let destinationOperand' := evalSigned destinationOperand bits
        match msb with
          | Msb.bpf_jne=> destinationOperand' != sourceOperandTrimmed'
          | Msb.bpf_jeq=> destinationOperand' == sourceOperandTrimmed'
          | Msb.bpf_jlt=> destinationOperand' < sourceOperandTrimmed'
          | Msb.bpf_jle=> destinationOperand' <= sourceOperandTrimmed'
          | Msb.bpf_jgt=> destinationOperand' > sourceOperandTrimmed'
          | Msb.bpf_jge=> destinationOperand' >= sourceOperandTrimmed'
          | Msb.bpf_jset=> (andLogical destinationOperand' sourceOperandTrimmed') != 0
          -- Operadores condicionais Signed, trata ambos valores como negativos
          -- Uso a função returnSigned para obter o valor absoluto
          | Msb.bpf_jsge=> (returnSigned destinationOperand bits)<= (returnSigned sourceOperandTrimmed bits)
          | Msb.bpf_jsgt=> (returnSigned destinationOperand bits) < (returnSigned sourceOperandTrimmed bits)
          | Msb.bpf_jsle=> (returnSigned destinationOperand bits) >= (returnSigned sourceOperandTrimmed bits)
          | Msb.bpf_jslt=> (returnSigned destinationOperand bits) > (returnSigned sourceOperandTrimmed bits)
          | Msb.bpf_ja  => true
          | _ => false

def execJmp (instr : Instructions) (word : Word) : Instructions :=
  match word with
  | Word.mk imm offset srcReg destReg opCode =>
    match instr, offset with
     | Instructions.Cons _ _, Offset.mk 0 => instr
     | Instructions.Cons _w ws, Offset.mk off => execJmp ws (Word.mk imm (Offset.mk (off-1)) srcReg destReg opCode)
     | Instructions.Nil _w, Offset.mk _ => Instructions.Nil (Word.mk imm offset srcReg destReg OpCode.Eof)
     | _, _ => Instructions.Nil (Word.mk imm offset srcReg destReg OpCode.Eof)

def applyMainCall (main : MemorySpace → Registers → Instructions → ℕ → MemorySpace × Registers × Instructions ) (stack : MemorySpace) (regs : Registers) (instr : Instructions) (fuel : ℕ ) : Registers :=
  let (_retFuncStack,retFuncRegs,_retFuncInstr) := main stack regs instr fuel
  retFuncRegs

def applyWordJmp (_stack : MemorySpace) (regs : Registers) (instr : Instructions) (word : Word) (bits : ℕ ) : Instructions × Registers :=
  match word with
  | Word.mk _imm _offset _srcReg _destReg opCode =>
    match opCode with
      |OpCode.Eof => (instr, regs)
      | _ =>
        match (evalJmpCond regs word bits) with
          | true => (execJmp instr word, regs)
          | false => (instr, regs)

def exeMain (stack : MemorySpace) (regs : Registers) (instr : Instructions) (fuel : ℕ) : MemorySpace × Registers × Instructions :=
  let regs := if fuel == 1000 then updateRegisters regs stack else regs
  match fuel with
  | 0 => (stack, regs, instr)  -- Retorna o estado atual sem executar mais instruções
  | fuel' + 1 =>
      match instr with
      | Instructions.Nil _word => (stack, regs, instr)  -- Programa terminou
      | Instructions.Cons word instr' =>
        match word with
        | Word.mk _imm _offset _srcReg _destReg opCode =>
          match opCode with
          | OpCode.Eof => (stack, regs, instr)  -- Parar execução no EOF
          | OpCode.mk _msb _source lsb =>
            match lsb with
            | Lsb.bpf_alu =>
              -- Operações que alteram os registradores
              let regs' := applyWordAlu regs word 32
              exeMain stack regs' instr' fuel'

            | Lsb.bpf_alu64 =>
              -- Operações que alteram os registradores
              let regs' := applyWordAlu regs word 64
              exeMain stack regs' instr' fuel'

            | Lsb.bpf_ld | Lsb.bpf_ldx =>
              -- Operações que alteram a memória
              let regs' := applyWordMemoryLD regs stack word
              exeMain stack regs' instr' fuel'

            | Lsb.bpf_st =>
              -- Operações que alteram a memória
              let stack' := applyWordMemoryST regs stack word
              exeMain stack' regs instr' fuel'

            | Lsb.bpf_stx =>
              -- Operações que alteram a memória
              let stack' := applyWordMemoryST regs stack word
              exeMain stack' regs instr' fuel'

            | Lsb.bpf_jmp32 =>
              -- Operações de salto que alteram as instruções
              let (instr'', regs') := applyWordJmp stack regs instr' word 32
              exeMain stack regs' instr'' fuel'

            | Lsb.bpf_jmp =>
              -- Operações de salto que alteram as instruções
              match word with
              | Word.mk _imm _offset _srcReg _destReg (OpCode.mk Msb.bpf_call_local _source _lsb) => -- Caso seja um call chamo a função
                let funcInstr := execJmp instr word -- Faço um jump até a posição da função
                let (_retFuncStack,retFuncRegs,_retFuncInstr) := exeMain stack regs funcInstr fuel'-- Executo a função e recebo os valores de retorno
                exeMain stack (updateRegistersCall regs retFuncRegs) (consumeIntructionList instr 1) fuel'
                -- Na linha acima, atualiza o valor de r0 retornado pela função
                -- Consome uma instrução na lista de instruçoes
                -- E por ultimo segue a execução do Main
              | _ =>  let (instr'', regs') := applyWordJmp stack regs instr' word 64
                      exeMain stack regs' instr'' fuel'


def exeMainDebug (stack : MemorySpace) (regs : Registers) (instr : Instructions) (fuel : ℕ) (history: List ℕ ) : MemorySpace × Registers × Instructions × List ℕ :=
  let regs := if fuel == 1000 then updateRegisters regs stack else regs
  match fuel with
  | 0 => (stack, regs, instr,history)  -- Retorna o estado atual sem executar mais instruções
  | fuel' + 1 =>
      match instr with
      | Instructions.Nil _word => (stack, regs, instr,history)  -- Programa terminou
      | Instructions.Cons word instr' =>
        match word with
        | Word.mk _imm _offset _srcReg _destReg opCode =>
          match opCode with
          | OpCode.Eof => (stack, regs, instr,history)  -- Parar execução no EOF
          | OpCode.mk _msb _source lsb =>
            match lsb with
            | Lsb.bpf_alu =>
              -- Operações que alteram os registradores
              let regs' := applyWordAlu regs word 32
              let history' := regs'.r0 :: history
              exeMainDebug stack regs' instr' fuel' history'

            | Lsb.bpf_alu64 =>
              -- Operações que alteram os registradores
              let regs' := applyWordAlu regs word 64
              let history' := regs'.r0 :: history
              exeMainDebug stack regs' instr' fuel' history'

            | Lsb.bpf_ld | Lsb.bpf_ldx =>
              -- Operações que alteram a memória
              let regs' := applyWordMemoryLD regs stack word
              let history' := regs'.r0 :: history
              exeMainDebug stack regs' instr' fuel' history'

            | Lsb.bpf_st =>
              -- Operações que alteram a memória
              let stack' := applyWordMemoryST regs stack word
              let history' := regs.r0 :: history
              exeMainDebug stack' regs instr' fuel' history'

            | Lsb.bpf_stx =>
              -- Operações que alteram a memória
              let stack' := applyWordMemoryST regs stack word
              let history' := regs.r0 :: history
              exeMainDebug stack' regs instr' fuel' history'

            | Lsb.bpf_jmp32 =>
              -- Operações de salto que alteram as instruções
              let (instr'', regs') := applyWordJmp stack regs instr' word 32
              let history' := regs.r0 :: history
              exeMainDebug stack regs' instr'' fuel' history'

            | Lsb.bpf_jmp =>
              -- Operações de salto que alteram as instruções
              match word with
              | Word.mk _imm _offset _srcReg _destReg (OpCode.mk Msb.bpf_call_local _source _lsb) => -- Caso seja um call chamo a função
                let funcInstr := execJmp instr word -- Faço um jump até a posição da função
                let (_retFuncStack,retFuncRegs,_retFuncInstr) := exeMain stack regs funcInstr fuel'-- Executo a função e recebo os valores de retorno
                let history' := regs.r0 :: history
                exeMainDebug stack (updateRegistersCall regs retFuncRegs) (consumeIntructionList instr 1) fuel' history'
                -- Na linha acima, atualiza o valor de r0 retornado pela função
                -- Consome uma instrução na lista de instruçoes
                -- E por ultimo segue a execução do Main
              | _ =>  let (instr'', regs') := applyWordJmp stack regs instr' word 64
                      let history' := regs.r0 :: history
                      exeMainDebug stack regs' instr'' fuel' history'
