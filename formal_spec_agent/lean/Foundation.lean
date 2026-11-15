import Std

/- Trusted semantic definitions for a deliberately small Protocol IR fragment.
   List (Fin 256) represents finite octet buffers; Int is the IR integer domain.
   This file does not model C memory, checked signed64 arithmetic or scheduling. -/
namespace FormalSpecAgent

abbrev Byte := Fin 256
abbrev Bytes := List Byte

def byteAt (data : Bytes) (offset : Int) : Int :=
  if offset < 0 then 0 else Int.ofNat (data.getD offset.toNat 0).val

def byteSlice (data : Bytes) (offset count : Int) : Bytes :=
  (data.drop offset.toNat).take count.toNat

end FormalSpecAgent
