import «EBPFSpec».Semantic

-- Converte um número natural para uma lista de bits (binário)
def natToBinAux (n : Nat) (fuel : Nat) : List Bool :=
match fuel with
| 0 => []
| fuel' + 1 =>
  match n with
  | 0 => []
  | _ => (n % 2 == 1) :: (natToBinAux (n / 2) fuel')

-- Converte um número natural para uma lista de bits
def natToBin (n : Nat) : List Bool :=
  List.reverse ( natToBinAux n (n*2))

-- Realiza a operação AND bit a bit entre duas listas de bits
def bitwiseAnd (a b : List Bool) : List Bool :=
  let len := max a.length b.length
  let aPadded := List.replicate (len - a.length) false ++ a
  let bPadded := List.replicate (len - b.length) false ++ b
  List.zipWith (· && ·) aPadded bPadded


-- Converte uma lista de bits de volta para um número natural
def binToNat (bits : List Bool) : Nat :=
  bits.foldl (fun acc b => acc * 2 + if b then 1 else 0) 0


-- Função principal que faz a operação AND lógica bit a bit
def andLogical (x y : Nat) : Nat :=
  let binX := natToBin x
  let binY := natToBin y
  let resultBin := bitwiseAnd binX binY
  binToNat resultBin


def bitwiseOr (a b : List Bool) : List Bool :=
  let len := max a.length b.length
  let aPadded := List.replicate (len - a.length) false ++ a
  let bPadded := List.replicate (len - b.length) false ++ b
  List.zipWith (· || ·) aPadded bPadded

-- Função principal que faz a operação OR lógica bit a bit
def orLogical (x y : Nat) : Nat :=
  let binX := natToBin x
  let binY := natToBin y
  let resultBin := bitwiseOr binX binY
  binToNat resultBin

-- Realiza a operação XOR bit a bit entre duas listas de bits
def bitwiseXor (a b : List Bool) : List Bool :=
  let len := max a.length b.length
  let aPadded := List.replicate (len - a.length) false ++ a
  let bPadded := List.replicate (len - b.length) false ++ b
  List.zipWith (fun x y => x != y) aPadded bPadded

-- Função principal que faz a operação XOR lógica bit a bit
def xorLogical (x y : Nat) : Nat :=
  let binX := natToBin x
  let binY := natToBin y
  let resultBin := bitwiseXor binX binY
  binToNat resultBin

def bitTrim (n size: ℕ) : ℕ :=
  let binaryValue := natToBin n
  let wordSize := binaryValue.length
  if wordSize <= size then (binToNat binaryValue)
  else binToNat ( binaryValue.drop (wordSize - size))

def leftShift  (n shift bits : ℕ) : ℕ :=
  let list := natToBin n
  let shift := if shift <= bits then shift else shift % bits -- Tratar valores de Shift maiores que o tamanho da operação
  let padding := List.replicate (shift) false
  binToNat (list ++ padding)

def rightShift  (n shift bits : ℕ) : ℕ :=
  let list := natToBin n
  let listSize := list.length
  let shift := if shift <= bits then shift else shift % bits -- Tratar valores de Shift maiores que o tamanho da operação
  let listCutted := list.take ( listSize - shift )
  let padding := List.replicate shift false
  binToNat ( padding ++ listCutted)

def assignedRightShift  (n shift bits : ℕ) : ℕ :=
  let list := natToBin n
  let listSize := list.length
  let shift := if shift <= bits then shift else shift % bits -- Tratar valores de Shift maiores que o tamanho da operação
  let listCutted := list.take ( listSize - shift )
  let padding := List.replicate shift true
  binToNat ( padding ++ listCutted)


def negBinary (list : List Bool) : List Bool :=
  list.map (λ f=> if f = false then true else false)

def negCast (n bits : ℕ) : ℕ :=
  let binaryValue := natToBin n
  let size := binaryValue.length
  let padding := List.replicate (bits - size) true
  let n' := binToNat (padding ++ negBinary binaryValue)
  bitTrim (n'+ 1) bits

def makeSigned (n bits: ℕ) : ℕ :=
  let binaryValue := natToBin n
  let size := binaryValue.length
  let padding := List.replicate (bits - size) true
  let n' := binToNat ((padding ++ negBinary binaryValue))
  if size == bits then n else bitTrim (n'+ 1) bits


def returnSigned (n bits : ℕ) : ℕ :=
  let size := (natToBin n).length
  let n':= if size == bits then n else bitTrim (n - 1) bits
  let incr := if size == bits then 1 else 0
  bitTrim (binToNat ( negBinary ((natToBin n')) ) + incr ) bits

def signedMod (x y bits : ℕ ) : ℕ :=
  let flagX := (((natToBin x).headD true) == true) &&  ((natToBin x).length == bits) --Se o bit de sinal(32) foi true
  let x':= if flagX then (returnSigned x bits) else x --Verifica se o operador x é negativo
  let flagY := (((natToBin y).headD true) == true) &&  ((natToBin y).length == bits) --Se o bit de sinal(32) foi true
  let y':= if flagY then (returnSigned y bits) else y --Verifica se o operador y é negativo
  if flagX then makeSigned (x' % y') bits else (x' % y') -- Retorna negativo caso X seja negativo

def signedDivision (x y bits : ℕ ) : ℕ :=
  let flagX := (((natToBin x).headD true) == true) &&  ((natToBin x).length == bits) --Se o bit de sinal(32) foi true
  let x':= if flagX then (returnSigned x bits) else x --Verifica se o operador x é negativo
  let flagY := (((natToBin y).headD true) == true) &&  ((natToBin y).length == bits) --Se o bit de sinal(32) foi true
  let y':= if flagY then (returnSigned y bits) else y --Verifica se o operador y é negativo
  if flagX || flagY then makeSigned (x' / y') bits else (x' / y') -- Retorna negativo caso X seja negativo


def emptyMemory : MemorySpace :=
  { data := fun _ => 0 }

def readReg (regs : Registers) (r : RegisterCode) : Nat :=
  match r with
  | RegisterCode.r0 => regs.r0
  | RegisterCode.r1 => regs.r1
  | RegisterCode.r2 => regs.r2
  | RegisterCode.r3 => regs.r3
  | RegisterCode.r4 => regs.r4
  | RegisterCode.r5 => regs.r5
  | RegisterCode.r6 => regs.r6
  | RegisterCode.r7 => regs.r7
  | RegisterCode.r8 => regs.r8
  | RegisterCode.r9 => regs.r9
  | RegisterCode.r10 => regs.r10
  | _ => 0

def writeReg (regs : Registers) (r : RegisterCode) (val : Nat) : Registers :=
  match r with
  | RegisterCode.r0 => { regs with r0 := val }
  | RegisterCode.r1 => { regs with r1 := val }
  | RegisterCode.r2 => { regs with r2 := val }
  | RegisterCode.r3 => { regs with r3 := val }
  | RegisterCode.r4 => { regs with r4 := val }
  | RegisterCode.r5 => { regs with r5 := val }
  | RegisterCode.r6 => { regs with r6 := val }
  | RegisterCode.r7 => { regs with r7 := val }
  | RegisterCode.r8 => { regs with r8 := val }
  | RegisterCode.r9 => { regs with r9 := val }
  | RegisterCode.r10 => { regs with r10 := val }
  | _ => regs



-- Convert a hexadecimal character to a natural number
def hexCharToNat (c : Char) : Nat :=
  if '0' ≤ c ∧ c ≤ '9' then
    Char.toNat c - Char.toNat '0'
  else if 'a' ≤ c ∧ c ≤ 'f' then
    10 + Char.toNat c - Char.toNat 'a'
  else if 'A' ≤ c ∧ c ≤ 'F' then
    10 + Char.toNat c - Char.toNat 'A'
  else
    panic! s!"Invalid hexadecimal character: {c}"

-- Convert a list of hexadecimal characters to a natural number
def hexToNatList (s : List Char) (acc : Nat) : Nat :=
  match s with
  | [] => acc
  | c :: rest =>
    let n := hexCharToNat c
    hexToNatList rest (16 * acc + n)

-- Convert a hexadecimal string to a natural number
def hexToNat (s : String) : Nat :=
  hexToNatList s.toList 0

-- Converte um número (0-15) para o caractere hexadecimal correspondente
def natToHexChar (n : ℕ) : Char :=
  if n < 10 then
    Char.ofNat (n + 48)  -- '0' é representado por 48 na tabela ASCII
  else
    Char.ofNat (n - 10 + 97)  -- 'a' é representado por 97 na tabela ASCII

-- Função recursiva para gerar a representação hexadecimal como uma lista de caracteres
def natToHexRec (n : ℕ) : List Char :=
  if n = 0 then []
  else natToHexRec (n / 16) ++ [natToHexChar (n % 16)]

-- Função principal que lida com o caso em que n = 0
def natToHexCharList (n : ℕ) : List Char :=
  if n = 0 then ['0']
  else natToHexRec n

def natToHexString (n : ℕ) : String :=
  if n = 0 then String.mk ['0']
  else String.mk (natToHexRec n)

def getDestCode (destReg : DestinationReg) :  RegisterCode  :=
  match destReg with
    | DestinationReg.mk x => x

def getSrcCode (srcReg : SourceReg) :  RegisterCode  :=
  match srcReg with
    | SourceReg.mk x => x

def getNatCont (cont : Content) :  ℕ  :=
  match cont with
    | Content.mk nat => nat

def getNatImm (imm : Immediate) :  ℕ  :=
  match imm with
    | Immediate.mk nat => nat
    | Immediate.mkN nat => nat

def getNatOffset (off : Offset) (n : ℕ ) :  ℕ  :=
  match off with
    | Offset.mk nat => nat + n
    | Offset.mkN nat => n - nat
    | _ => 0

def writeMem (mem : MemorySpace) (addr : Fin 513) (val : Nat) : MemorySpace :=
  { data := fun i => if i = addr then val else mem.data i }

def readMem (mem : MemorySpace) (addr : Fin 513) : Nat :=
  mem.data addr

-- Le o espaço de memoria retornando o valor natural contido no indice index
def readMemNat (mem : MemorySpace) (index : Nat) : Nat :=
  mem.data (⟨ index % 513, by {
  have h : index % 513 < 513 := Nat.mod_lt index (by decide)
  exact h
}⟩)

theorem provaFin (index : Nat) : index % 513 < 513 := by
  -- Introduce the fact using `have`
  have h : index % 513 < 513 := Nat.mod_lt index (by decide)
  -- Use the fact to prove the goal
  exact h

def createStackMemoryAux (index : ℕ )(stack : MemorySpace) (input : StackWord) (cont : ℕ ) : MemorySpace :=
  match input with
  | StackWord.mk charA charB rest =>
    let value := hexToNatList [charA,charB] 0
    createStackMemoryAux (index + 1) (writeMem stack ⟨ index % 513, provaFin index⟩ value) rest (cont+2)
  | StackWord.nil => (writeMem stack ⟨ 512 % 513, provaFin 512⟩ (cont) )

def createStackMemory (index : ℕ )(stack : MemorySpace) (input : StackWord) : MemorySpace :=
  createStackMemoryAux index stack input 0

def createStackMemoryCharList (index : ℕ )(stack : MemorySpace) (input : List Char) : MemorySpace :=
  match input with
  | charA :: charB :: rest =>
    let value := hexToNatList [charA,charB] 0
    createStackMemoryCharList (index + 1) (writeMem stack ⟨ index % 513, provaFin index⟩ value) rest
  | _ :: [] => stack
  | [] => stack

--Passar tamanho da palavra -1
--Começa a obter os valores a partir do indice passado e guarda a palavra de forma inversa igual ao subnet
def returnMemoryBlockChar ( stack : MemorySpace ) ( index: ℕ ) ( size : ℕ ) : List Char  :=
  match size with
  | 0 =>
    let n := natToHexCharList (readMemNat stack index)
    match n.length with
    | 1 => '0' :: n
    | _ => n
  | size' + 1 =>
    let valRet:= (returnMemoryBlockChar stack (index+1) size')
    let valChar := natToHexCharList (readMemNat stack index)
    match valChar.length with
    | 1 => valRet ++ ('0' :: valChar)
    | _ => valRet ++ valChar

def returnMemoryBlockNat ( stack : MemorySpace ) ( index: ℕ ) ( size : ℕ ) : ℕ  :=
  hexToNatList (returnMemoryBlockChar stack index size) 0

def natToNatListAux (input : List Char ) : List ℕ :=
  match input with
    | x :: y :: zs => ( hexToNatList (x :: y :: []) 0 ) :: natToNatListAux zs
    | x :: zs => ( hexToNatList ( '0' :: x :: []) 0 ) :: natToNatListAux zs
    | _ => []

def natToNatList (input : ℕ ) : List ℕ :=
    natToNatListAux (natToHexCharList input)


def returnMemoryBlock (regs : Registers) (stack : MemorySpace) (word : Word) : Registers :=
  match word with
    | Word.mk imm offset srcReg destReg (OpCode.mk msb src _lsb) =>
      let indexSrc := if src = Source.bpf_k then 0 else readReg regs (getSrcCode srcReg)
      let offsetVal := getNatOffset offset indexSrc
      match msb with
      | Msb.bpf_ldxb => writeReg regs (getDestCode destReg) (returnMemoryBlockNat stack offsetVal 0)
      | Msb.bpf_ldxh => writeReg regs (getDestCode destReg) (returnMemoryBlockNat stack offsetVal 1)--2
      | Msb.bpf_ldxw => writeReg regs (getDestCode destReg) (returnMemoryBlockNat stack offsetVal 3)
      | Msb.bpf_ldxdw => writeReg regs (getDestCode destReg) (returnMemoryBlockNat stack offsetVal 7)
      | Msb.bpf_lddw => writeReg regs (getDestCode destReg) (getNatImm imm)
      | _ => regs
    |_ => regs

def updateRegisters (regs : Registers) (stack : MemorySpace) : Registers:=
  let val := (returnMemoryBlockNat stack 512 0)
  writeReg regs RegisterCode.r10 val

def writeMemoryBlockAux (stack : MemorySpace) (index : ℕ ) (values : List ℕ ): MemorySpace :=
  match values with
  | [] => stack  -- Quando não há mais valores a escrever, retorna a memória final
  | v :: vs =>
      let updatedStack := writeMem stack ⟨ index % 513, provaFin index ⟩ v
      writeMemoryBlockAux updatedStack (index+1) vs -- Chama recursivamente para escrever os próximos valores

def writeMemoryBlock (stack : MemorySpace) (index : ℕ ) (values : List ℕ ) (size : ℕ ) : MemorySpace :=
  let listSize := values.length
  let padding :=  (size +1 ) - listSize
  let paddedValues := (values.reverse) ++ List.replicate padding 0
  writeMemoryBlockAux stack index paddedValues

def byteSwapInstructionLe (input size: ℕ ) : ℕ :=
  let binaryInput := natToHexCharList input
  let paddingSize := if binaryInput.length < size then size - binaryInput.length else 0
  let padding := List.replicate (paddingSize) '0'
  let paddedList :=  (binaryInput ++ padding)
  let paddedListReverse :=  paddedList.reverse
  let binaryInputCutted := paddedListReverse.take ( size )
  let binaryInputReverse := binaryInputCutted.reverse
  hexToNatList binaryInputReverse 0

def reverseHexList (list : List Char) : List Char :=
  match list with
  | x :: y :: zs => reverseHexList zs ++ (x :: y :: [])
  | _ :: [] => []
  | [] => []

def byteSwapInstructionBe (input size: ℕ ) : ℕ :=
  let binaryInput := natToHexCharList input -- Transforma de Natural para Lista de Hexadecimais
  let binaryInputSize := binaryInput.length -- Captura o tamanho da lista transformada
  let binaryInput := if binaryInputSize > size then binaryInput.drop (binaryInputSize - size) else binaryInput
  let paddingSize := if binaryInputSize < size then size - binaryInput.length else 0 --Calcula o tamanho do Padding
  let padding := List.replicate (paddingSize) '0' -- Cria a lista de valores nulos para o padding
  let paddedList :=  (padding ++ binaryInput ) -- Cria a lista de valores já com o preenchimento
  let paddedListBe16 :=  reverseHexList paddedList
  hexToNatList paddedListBe16 0

def byteSwapInstructionSwap (input size: ℕ ) : ℕ :=
  let binaryInput := natToHexCharList input -- Transforma de Natural para Lista de Hexadecimais
  let binaryInputSize := binaryInput.length -- Captura o tamanho da lista transformada
  let binaryInput := if binaryInputSize > size then binaryInput.drop (binaryInputSize - size) else binaryInput
  let paddingSize := if binaryInputSize < size then size - binaryInput.length else 0 --Calcula o tamanho do Padding
  let padding := List.replicate (paddingSize) '0' -- Cria a lista de valores nulos para o padding
  let paddedList :=  (padding ++ binaryInput ) -- Cria a lista de valores já com o preenchimento
  let paddedListSwap :=  reverseHexList paddedList
  hexToNatList paddedListSwap 0

-- Função que expande de index1 para index2 bits, preservando o sinal
def movsx (n index1 index2: Nat) : Nat :=
  let binaryList := natToBin n       -- Converte para binário
  let binaryListIndex1 := binaryList.drop (binaryList.length - index1)    -- Pega os index1 bits menos significativos
  let signBit := binaryListIndex1.headD false  -- Pega o bit de sinal (mais significativo dos 16 bits)

  -- Expande para 32 bits: se o bit de sinal for 1, preenche com 1s; caso contrário, com 0s
  let binaryListIndex2 := List.replicate (index2 - binaryListIndex1.length) signBit ++ binaryListIndex1
  binToNat binaryListIndex2

def evalSigned(x _bits : ℕ ) : ℕ :=
  let flagX := (((natToBin x).headD true) == true) &&  (((natToBin x).length == 32) || ((natToBin x).length == 64)) --Se o bit de sinal(32) foi true
  let bitsSize := if ((natToBin x).length == 32) then 32 else 64
  if flagX then returnSigned x bitsSize else x -- Retorna negativo caso X seja negativo

def getRegAddress (reg : RegisterCode) : ℕ :=
  match reg with
  | RegisterCode.r0 => 0
  | RegisterCode.r1 => 1
  | RegisterCode.r2 => 2
  | RegisterCode.r3 => 3
  | RegisterCode.r4 => 4
  | RegisterCode.r5 => 5
  | RegisterCode.r6 => 6
  | RegisterCode.r7 => 7
  | RegisterCode.r8 => 8
  | RegisterCode.r9 => 9
  | RegisterCode.r10 => 10
  | _ => 0

def updateRegistersCall (regsMain regsLocal : Registers) : Registers :=
  writeReg regsMain RegisterCode.r0 (readReg regsLocal RegisterCode.r0)

def consumeIntructionList ( instr : Instructions) ( n : ℕ ) : Instructions :=
  match instr, n with
  | _ , 0 => instr
  | Instructions.Cons _w ws, n' + 1 => consumeIntructionList ws n'
  | Instructions.Nil _w, _n' + 1 => instr

def listCharBool (input : List Bool) : String :=
  match input with
  | [] => ""
  | x :: xs =>
   match x with
   | false => "0" ++ listCharBool xs
   | true =>  "1" ++ listCharBool xs
