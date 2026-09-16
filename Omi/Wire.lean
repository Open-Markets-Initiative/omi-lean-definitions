/-!
# Wire bytes

The field kinds the definitions are built from, each with an encoder, a decoder, and the lemmas
every message proof leans on: an encoding is as wide as its field says, and decoding what was
encoded gives the value back and leaves the following bytes alone.

Bytes are `List UInt8` rather than `ByteArray`: lists are what the proofs can take apart, and a
`ByteArray` converts at the edges.
-/

namespace Omi

/-- Big-endian bytes of the low `n` bytes of a natural number, most significant first -/
def beBytes : Nat → Nat → List UInt8
  | 0, _ => []
  | n + 1, v => beBytes n (v / 256) ++ [UInt8.ofNat (v % 256)]

/-- The natural number big-endian bytes spell -/
def beValue (bytes : List UInt8) : Nat :=
  bytes.foldl (fun acc byte => acc * 256 + byte.toNat) 0

theorem beBytes_length (n v : Nat) : (beBytes n v).length = n := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih => simp [beBytes, ih]

theorem beValue_append_byte (bytes : List UInt8) (byte : UInt8) :
    beValue (bytes ++ [byte]) = beValue bytes * 256 + byte.toNat := by
  simp [beValue, List.foldl_append]

/-- Big-endian bytes read back as the number, reduced to the width they hold -/
theorem beValue_beBytes (n v : Nat) : beValue (beBytes n v) = v % 256 ^ n := by
  induction n generalizing v with
  | zero => simp [beBytes, beValue, Nat.mod_one]
  | succ n ih =>
    have byte : (UInt8.ofNat (v % 256)).toNat = v % 256 := by simp
    rw [beBytes, beValue_append_byte, ih, byte]
    rw [Nat.pow_succ, Nat.mul_comm (256 ^ n) 256, Nat.mod_mul]
    omega

/-- Split off the first `n` bytes, when there are that many -/
def take? (n : Nat) (bytes : List UInt8) : Option (List UInt8 × List UInt8) :=
  if n ≤ bytes.length then some (bytes.take n, bytes.drop n) else none

/-- Taking exactly the bytes in front splits them from what follows. The width is a hypothesis rather
    than `front.length` itself, so a caller whose width is a type index never has to rewrite it -/
theorem take?_append {front rest : List UInt8} {n : Nat} (width : front.length = n) :
    take? n (front ++ rest) = some (front, rest) := by
  subst width
  simp [take?]

/-! ## Integers -/

/-- An unsigned big-endian integer `n` bytes wide; a signed field reads the same bits -/
def encodeUInt (n : Nat) (value : BitVec (8 * n)) : List UInt8 :=
  beBytes n value.toNat

def decodeUInt (n : Nat) (bytes : List UInt8) : Option (BitVec (8 * n) × List UInt8) :=
  (take? n bytes).map fun (front, rest) => (BitVec.ofNat (8 * n) (beValue front), rest)

@[simp] theorem encodeUInt_length (n : Nat) (value : BitVec (8 * n)) : (encodeUInt n value).length = n :=
  beBytes_length n value.toNat

theorem BitVec.toNat_lt_pow (n : Nat) (value : BitVec (8 * n)) : value.toNat < 256 ^ n := by
  have := value.isLt
  rwa [Nat.pow_mul] at this

@[simp] theorem decodeUInt_encodeUInt (n : Nat) (value : BitVec (8 * n)) (rest : List UInt8) :
    decodeUInt n (encodeUInt n value ++ rest) = some (value, rest) := by
  unfold decodeUInt
  rw [take?_append (encodeUInt_length n value)]
  simp [encodeUInt, beValue_beBytes, Nat.mod_eq_of_lt (BitVec.toNat_lt_pow n value)]

/-- A little-endian integer: the big-endian bytes reversed -/
def encodeUIntLE (n : Nat) (value : BitVec (8 * n)) : List UInt8 :=
  (beBytes n value.toNat).reverse

def decodeUIntLE (n : Nat) (bytes : List UInt8) : Option (BitVec (8 * n) × List UInt8) :=
  (take? n bytes).map fun (front, rest) => (BitVec.ofNat (8 * n) (beValue front.reverse), rest)

@[simp] theorem encodeUIntLE_length (n : Nat) (value : BitVec (8 * n)) : (encodeUIntLE n value).length = n := by
  simp [encodeUIntLE, beBytes_length]

@[simp] theorem decodeUIntLE_encodeUIntLE (n : Nat) (value : BitVec (8 * n)) (rest : List UInt8) :
    decodeUIntLE n (encodeUIntLE n value ++ rest) = some (value, rest) := by
  unfold decodeUIntLE
  rw [take?_append (encodeUIntLE_length n value)]
  simp [encodeUIntLE, beValue_beBytes, Nat.mod_eq_of_lt (BitVec.toNat_lt_pow n value)]

/-! ## Text -/

/-- Fixed-width ascii text, exactly as sent: padding is kept, so what is decoded encodes back unchanged -/
structure Alpha (n : Nat) where
  bytes : List UInt8
  length : bytes.length = n
  deriving DecidableEq

instance : Repr (Alpha n) where
  reprPrec alpha _ := repr (String.ofList (alpha.bytes.map fun byte => Char.ofNat byte.toNat))

def Alpha.encode (alpha : Alpha n) : List UInt8 :=
  alpha.bytes

def Alpha.decode (n : Nat) (bytes : List UInt8) : Option (Alpha n × List UInt8) :=
  if h : n ≤ bytes.length then
    some (⟨bytes.take n, by simp [List.length_take]; omega⟩, bytes.drop n)
  else
    none

@[simp] theorem Alpha.encode_length (alpha : Alpha n) : (Alpha.encode alpha).length = n :=
  alpha.length

@[simp] theorem Alpha.decode_encode (alpha : Alpha n) (rest : List UInt8) :
    Alpha.decode n (Alpha.encode alpha ++ rest) = some (alpha, rest) := by
  obtain ⟨bytes, length⟩ := alpha
  subst length
  simp [Alpha.decode, Alpha.encode]

/-! ## Repetition -/

/-- A counted run of items, each decoded by `item` -/
def decodeMany (item : List UInt8 → Option (α × List UInt8)) : Nat → List UInt8 → Option (List α × List UInt8)
  | 0, bytes => some ([], bytes)
  | n + 1, bytes => do
    let (first, bytes) ← item bytes
    let (others, bytes) ← decodeMany item n bytes
    pure (first :: others, bytes)

/-- Items each encoded by `encode`, back to back -/
def encodeMany (encode : α → List UInt8) (items : List α) : List UInt8 :=
  items.flatMap encode

/-- A counted run decodes back to its items when each item does -/
theorem decodeMany_encodeMany (encode : α → List UInt8) (decode : List UInt8 → Option (α × List UInt8))
    (roundtrip : ∀ item rest, decode (encode item ++ rest) = some (item, rest))
    (items : List α) (rest : List UInt8) :
    decodeMany decode items.length (encodeMany encode items ++ rest) = some (items, rest) := by
  induction items with
  | nil => simp [decodeMany, encodeMany]
  | cons first others ih =>
    simp only [encodeMany] at ih ⊢
    simp [decodeMany, List.append_assoc, roundtrip, ih]

/-- A run of constant width items is as long as the count says -/
theorem encodeMany_length_const (encode : α → List UInt8) (width : Nat)
    (fixed : ∀ item, (encode item).length = width) (items : List α) :
    (encodeMany encode items).length = items.length * width := by
  induction items with
  | nil => simp [encodeMany]
  | cons first others ih =>
    simp only [encodeMany, List.flatMap_cons, List.length_append, fixed, List.length_cons]
    simp only [encodeMany] at ih
    rw [ih, Nat.succ_mul, Nat.add_comm]

/-- A run of non-empty items has at least one byte per item -/
theorem encodeMany_length_ge (encode : α → List UInt8) (nonempty : ∀ item, (encode item).length > 0)
    (items : List α) : items.length ≤ (encodeMany encode items).length := by
  induction items with
  | nil => simp [encodeMany]
  | cons first others ih =>
    simp only [encodeMany, List.flatMap_cons, List.length_append, List.length_cons]
    simp only [encodeMany] at ih
    have := nonempty first
    omega

/-- A list whose length fits an `n` byte count, so a count written from it needs no side condition -/
def Bounded (n : Nat) (α : Type) := { items : List α // items.length < 256 ^ n }

instance [DecidableEq α] : DecidableEq (Bounded n α) :=
  inferInstanceAs (DecidableEq { items : List α // items.length < 256 ^ n })

instance [Repr α] : Repr (Bounded n α) where
  reprPrec bounded precedence := reprPrec bounded.val precedence

theorem Bounded.length_lt (bounded : Bounded n α) : bounded.val.length < 256 ^ n :=
  bounded.property

/-- Rebuilding a bounded list from its items and any proof gives the list back -/
@[simp] theorem Bounded.mk_val (bounded : Bounded n α) (fits : bounded.val.length < 256 ^ n) :
    (⟨bounded.val, fits⟩ : Bounded n α) = bounded :=
  rfl

/-- Items decoded until the bytes run out, each decoder call handed at most `fuel` more turns -/
def decodeAll (item : List UInt8 → Option (α × List UInt8)) : Nat → List UInt8 → Option (List α)
  | _, [] => some []
  | 0, _ :: _ => none
  | fuel + 1, bytes => do
    let (first, rest) ← item bytes
    let others ← decodeAll item fuel rest
    pure (first :: others)

/-- Every item is at least a byte, so a run of items decodes back with fuel to spare -/
theorem decodeAll_encodeMany (encode : α → List UInt8) (decode : List UInt8 → Option (α × List UInt8))
    (roundtrip : ∀ item rest, decode (encode item ++ rest) = some (item, rest))
    (nonempty : ∀ item, (encode item).length > 0)
    (items : List α) (fuel : Nat) (enough : items.length ≤ fuel) :
    decodeAll decode fuel (encodeMany encode items) = some items := by
  induction items generalizing fuel with
  | nil => cases fuel <;> simp [decodeAll, encodeMany]
  | cons first others ih =>
    cases fuel with
    | zero => simp at enough
    | succ fuel =>
      simp only [encodeMany, List.flatMap_cons]
      have long : (encode first ++ List.flatMap encode others).length > 0 := by
        rw [List.length_append]
        have := nonempty first
        omega
      obtain ⟨byte, tail, spelled⟩ : ∃ byte tail, encode first ++ List.flatMap encode others = byte :: tail := by
        cases h : encode first ++ List.flatMap encode others with
        | nil => rw [h] at long; simp at long
        | cons byte tail => exact ⟨byte, tail, rfl⟩
      rw [spelled]
      have step := roundtrip first (List.flatMap encode others)
      rw [spelled] at step
      have more := ih fuel (by simpa using enough)
      simp only [encodeMany] at more
      simp [decodeAll, step, more]

/-! ## Framing -/

/-- A length prefix of `n` big endian bytes holding the body's length plus `offset`, then the body -/
def encodeFramed (n offset : Nat) (encode : α → List UInt8) (item : α) : List UInt8 :=
  encodeUInt n (BitVec.ofNat (8 * n) ((encode item).length + offset)) ++ encode item

/-- Read the prefix, take the bytes it counts, and decode them as one whole body -/
def decodeFramed (n offset : Nat) (decode : List UInt8 → Option (α × List UInt8)) (bytes : List UInt8) :
    Option (α × List UInt8) := do
  let (length, bytes) ← decodeUInt n bytes
  let (body, rest) ← take? (length.toNat - offset) bytes
  let (item, tail) ← decode body
  guard tail.isEmpty
  pure (item, rest)

theorem decodeFramed_encodeFramed (n offset : Nat) (encode : α → List UInt8)
    (decode : List UInt8 → Option (α × List UInt8))
    (roundtrip : ∀ item rest, decode (encode item ++ rest) = some (item, rest))
    (fits : ∀ item, (encode item).length + offset < 256 ^ n)
    (item : α) (rest : List UInt8) :
    decodeFramed n offset decode (encodeFramed n offset encode item ++ rest) = some (item, rest) := by
  have bound : (encode item).length + offset < 2 ^ (8 * n) := by
    rw [Nat.pow_mul]
    exact fits item
  have whole := roundtrip item []
  rw [List.append_nil] at whole
  unfold decodeFramed encodeFramed
  rw [List.append_assoc, decodeUInt_encodeUInt]
  simp only [Bind.bind, Option.bind_some, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt bound, Nat.add_sub_cancel, take?_append rfl]
  simp [whole, guard]

theorem encodeFramed_length (n offset : Nat) (encode : α → List UInt8) (item : α) :
    (encodeFramed n offset encode item).length = n + (encode item).length := by
  simp [encodeFramed]

/-- The little endian frame: the same prefix, low byte first -/
def encodeFramedLE (n offset : Nat) (encode : α → List UInt8) (item : α) : List UInt8 :=
  encodeUIntLE n (BitVec.ofNat (8 * n) ((encode item).length + offset)) ++ encode item

def decodeFramedLE (n offset : Nat) (decode : List UInt8 → Option (α × List UInt8)) (bytes : List UInt8) :
    Option (α × List UInt8) := do
  let (length, bytes) ← decodeUIntLE n bytes
  let (body, rest) ← take? (length.toNat - offset) bytes
  let (item, tail) ← decode body
  guard tail.isEmpty
  pure (item, rest)

theorem decodeFramedLE_encodeFramedLE (n offset : Nat) (encode : α → List UInt8)
    (decode : List UInt8 → Option (α × List UInt8))
    (roundtrip : ∀ item rest, decode (encode item ++ rest) = some (item, rest))
    (fits : ∀ item, (encode item).length + offset < 256 ^ n)
    (item : α) (rest : List UInt8) :
    decodeFramedLE n offset decode (encodeFramedLE n offset encode item ++ rest) = some (item, rest) := by
  have bound : (encode item).length + offset < 2 ^ (8 * n) := by
    rw [Nat.pow_mul]
    exact fits item
  have whole := roundtrip item []
  rw [List.append_nil] at whole
  unfold decodeFramedLE encodeFramedLE
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE]
  simp only [Bind.bind, Option.bind_some, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt bound, Nat.add_sub_cancel, take?_append rfl]
  simp [whole, guard]

theorem encodeFramedLE_length (n offset : Nat) (encode : α → List UInt8) (item : α) :
    (encodeFramedLE n offset encode item).length = n + (encode item).length := by
  simp [encodeFramedLE]

end Omi