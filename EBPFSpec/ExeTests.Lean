import «EBPFSpec».TestFunctions


------------------------------------------------------------------------------
/-
Only allow ARP packets:

         ldh [12]
         jne #0x806, drop -- Jump Not Equal
         ret #-1
         drop: ret #0
-/
-- Usar %r1 como o Acumulador
-- Substituir o ret pelo exit
-- Trocar as labels pelo valor do Offset
-- Valor invertido devido a particularidades dos testes de Conformidade

def prog_only_arp : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
ldh %r1, [12]
mov32 %r0, 1
jne %r1, 0x0608, 1
exit
mov32 %r0, 0
exit
result
0x1
}
/-
#eval exeConformance prog_only_arp (inputPackgeGeneratorArp true)

#eval evaluateEbpfProg prog_only_arp (cratePackgesArp 5 10)
-/

-------------------------------------------------------------------------------
/-
Only allow IPV4 packets:

         ldh [12]
         jne #0x8, drop -- Jump Not Equal
         ret #-1
         drop: ret #0
-/
def prog_only_IPV44 : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
ldh %r1, [12]
mov32 %r0, 1
jne %r1, 0x0008, 1
exit
mov32 %r0, 0
exit
result
0x1
}
/-
#eval exeConformance prog_only_IPV44 (inputPackgeGeneratorIPv4 true)

#eval evaluateEbpfProg prog_only_IPV44 (cratePackgesIPV4 15 100)
-/


-----------------------------------------------------------------------------
/-
 Only allow IPv4 TCP packets:

         ldh [12] --Load half-word into A where A = 32 bit wide accumulator
         jne #0x800, drop
         ldb [23]
         jneq #6, drop
         ret #-1
         drop: ret #0
-/
-- Usar %r1 como o Acumulador
-- Substituir o ret pelo exit
-- Trocar as labels pelo valor do Offset
def prog_only_IPv4_TCP : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
ldh %r1, [12]
jne %r1, 0x0008, 1
mov32 %r0, 0
ldh %r1, [12]
jne %r1, 0x0006, 1
mov32 %r0, 0
mov32 %r0, 1
exit
result
0x0
}

/-
Only allow IPv4 TCP SSH traffic:

         ldh [12]
         jne #0x800, drop
         ldb [23]
         jneq #6, drop
         ldh [20]
         jset #0x1fff, drop
         ldxb 4 * ([14] & 0xf)
         ldh [x + 14]
         jeq #0x16, pass
         ldh [x + 16]
         jne #0x16, drop
         pass: ret #-1
         drop: ret #0
-/
-- Usar %r0 como o Acumulador
-- Substituir o ret pelo exit
-- Trocar as labels pelo valor do Offset

def prog_only_IPv4_SSH : TestEval :=
{exe|
# Copyright Big Switch Networks Inc
# SPDX_License_Identifier Apache_2_0
asm
mov32 %r0, 0
mov32 %r1, 2
add32 %r0, 1
add32 %r0, %r1
add32 %r0, %r0
add32 %r0, -3
exit
result
0x3
}
