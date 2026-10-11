import PathInputs.Chunk00
import PathInputs.Chunk01
import PathInputs.Chunk02
import PathInputs.Chunk03
import PathInputs.Chunk04
import PathInputs.Chunk05
import PathInputs.Chunk06
import PathInputs.Chunk07
import PathInputs.Chunk08
import PathInputs.Chunk09
import PathInputs.Chunk10
import PathInputs.Chunk11
import PathInputs.Chunk12
import PathInputs.Chunk13
import PathInputs.Chunk14
import PathInputs.Chunk15
import PathInputs.Chunk16
import PathInputs.Chunk17
import PathInputs.Chunk18
import PathInputs.Chunk19
import PathInputs.Chunk20
import PathInputs.Chunk21
import PathInputs.Chunk22
import PathInputs.Chunk23
import PathInputs.Chunk24
import PathInputs.Chunk25
import PathInputs.Chunk26
import PathInputs.Chunk27
import PathInputs.Chunk28
import PathInputs.Chunk29
import PathInputs.Chunk30
import PathInputs.Chunk31
import PathInputs.Chunk32
namespace LocalIdentifyingQ6
open CardinalityEncoding
theorem path_inputs_from_constraints (C : Code) (X : Nat → Bool) (hX : ∀ v : Vertex, X (v.val+1) = C v)
    (hC : Constraints C) (hz0 : C 0 = true) (hz1 : C 1 = true) (hz2 : C 2 = true)
    (hs : prefixCount X 64 ≤ 13) :
    Q6RUPPath.Inputs (fun n => assignment X n = true) :=
  { chunk0 := semanticChunk0 C X hX hC hz0 hz1 hz2 hs,
    chunk1 := semanticChunk1 C X hX hC hz0 hz1 hz2 hs,
    chunk2 := semanticChunk2 C X hX hC hz0 hz1 hz2 hs,
    chunk3 := semanticChunk3 C X hX hC hz0 hz1 hz2 hs,
    chunk4 := semanticChunk4 C X hX hC hz0 hz1 hz2 hs,
    chunk5 := semanticChunk5 C X hX hC hz0 hz1 hz2 hs,
    chunk6 := semanticChunk6 C X hX hC hz0 hz1 hz2 hs,
    chunk7 := semanticChunk7 C X hX hC hz0 hz1 hz2 hs,
    chunk8 := semanticChunk8 C X hX hC hz0 hz1 hz2 hs,
    chunk9 := semanticChunk9 C X hX hC hz0 hz1 hz2 hs,
    chunk10 := semanticChunk10 C X hX hC hz0 hz1 hz2 hs,
    chunk11 := semanticChunk11 C X hX hC hz0 hz1 hz2 hs,
    chunk12 := semanticChunk12 C X hX hC hz0 hz1 hz2 hs,
    chunk13 := semanticChunk13 C X hX hC hz0 hz1 hz2 hs,
    chunk14 := semanticChunk14 C X hX hC hz0 hz1 hz2 hs,
    chunk15 := semanticChunk15 C X hX hC hz0 hz1 hz2 hs,
    chunk16 := semanticChunk16 C X hX hC hz0 hz1 hz2 hs,
    chunk17 := semanticChunk17 C X hX hC hz0 hz1 hz2 hs,
    chunk18 := semanticChunk18 C X hX hC hz0 hz1 hz2 hs,
    chunk19 := semanticChunk19 C X hX hC hz0 hz1 hz2 hs,
    chunk20 := semanticChunk20 C X hX hC hz0 hz1 hz2 hs,
    chunk21 := semanticChunk21 C X hX hC hz0 hz1 hz2 hs,
    chunk22 := semanticChunk22 C X hX hC hz0 hz1 hz2 hs,
    chunk23 := semanticChunk23 C X hX hC hz0 hz1 hz2 hs,
    chunk24 := semanticChunk24 C X hX hC hz0 hz1 hz2 hs,
    chunk25 := semanticChunk25 C X hX hC hz0 hz1 hz2 hs,
    chunk26 := semanticChunk26 C X hX hC hz0 hz1 hz2 hs,
    chunk27 := semanticChunk27 C X hX hC hz0 hz1 hz2 hs,
    chunk28 := semanticChunk28 C X hX hC hz0 hz1 hz2 hs,
    chunk29 := semanticChunk29 C X hX hC hz0 hz1 hz2 hs,
    chunk30 := semanticChunk30 C X hX hC hz0 hz1 hz2 hs,
    chunk31 := semanticChunk31 C X hX hC hz0 hz1 hz2 hs,
    chunk32 := semanticChunk32 C X hX hC hz0 hz1 hz2 hs }
#print axioms path_inputs_from_constraints
end LocalIdentifyingQ6
