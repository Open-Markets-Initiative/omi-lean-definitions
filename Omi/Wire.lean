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

/-- The length of a list of items each at most `most` bytes -/
theorem encodeMany_length_le (encode : α → List UInt8) (most : Nat)
    (bounded : ∀ item, (encode item).length ≤ most) (items : List α) :
    (encodeMany encode items).length ≤ most * items.length := by
  induction items with
  | nil => simp [encodeMany]
  | cons first others ih =>
    simp only [encodeMany, List.flatMap_cons, List.length_append, List.length_cons]
    simp only [encodeMany] at ih
    have := bounded first
    rw [Nat.mul_add, Nat.mul_one]
    omega

/-- One byte of variable length data: the item of a list sized by a length field -/
def Byte.encode (byte : UInt8) : List UInt8 :=
  [byte]

def Byte.decode : List UInt8 → Option (UInt8 × List UInt8)
  | byte :: rest => some (byte, rest)
  | [] => none

@[simp] theorem Byte.encode_length (byte : UInt8) : (Byte.encode byte).length = 1 :=
  rfl

theorem Byte.encode_length_pos (byte : UInt8) : (Byte.encode byte).length > 0 := by
  rw [Byte.encode_length]
  decide

@[simp] theorem Byte.decode_encode (byte : UInt8) (rest : List UInt8) :
    Byte.decode (Byte.encode byte ++ rest) = some (byte, rest) :=
  rfl

/-- A list whose length fits an `n` byte count, so a count written from it needs no side condition.
    Reducible, so a proof may see through it to the list and its bound -/
abbrev Bounded (n : Nat) (α : Type) := { items : List α // items.length < 256 ^ n }

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

/-- A packed field some of whose bits are written from what follows it: the rest is carried, and
    those bits are clear in what is carried, so the two can be put back together -/
abbrev Masked (n : Nat) (mask : BitVec n) := { value : BitVec n // value &&& mask = 0 }

instance {n : Nat} {mask : BitVec n} : DecidableEq (Masked n mask) :=
  inferInstanceAs (DecidableEq { value : BitVec n // value &&& mask = 0 })

instance {n : Nat} {mask : BitVec n} : Repr (Masked n mask) where
  reprPrec masked precedence := reprPrec masked.val precedence

theorem Masked.clear {n : Nat} {mask : BitVec n} (masked : Masked n mask) : masked.val &&& mask = 0 :=
  masked.property

/-- A list whose encodings together fit under an `n` byte length, so a length written from them
    needs no side condition: entries filling the bytes a length field states -/
abbrev Sized (n : Nat) (encode : α → List UInt8) := { items : List α // (encodeMany encode items).length < 256 ^ n }

instance [DecidableEq α] {encode : α → List UInt8} : DecidableEq (Sized n encode) :=
  inferInstanceAs (DecidableEq { items : List α // (encodeMany encode items).length < 256 ^ n })

instance [Repr α] {encode : α → List UInt8} : Repr (Sized n encode) where
  reprPrec sized precedence := reprPrec sized.val precedence

theorem Sized.length_lt {encode : α → List UInt8} (sized : Sized n encode) : (encodeMany encode sized.val).length < 256 ^ n :=
  sized.property

/-- A list of exactly `n` items: a group the protocol repeats a fixed number of times -/
abbrev Exact (n : Nat) (α : Type) := { items : List α // items.length = n }

instance [DecidableEq α] : DecidableEq (Exact n α) :=
  inferInstanceAs (DecidableEq { items : List α // items.length = n })

instance [Repr α] : Repr (Exact n α) where
  reprPrec exact precedence := reprPrec exact.val precedence

theorem Exact.length_eq (exact : Exact n α) : exact.val.length = n :=
  exact.property

/-- A fixed count reads an exact list back: the decoder reads as many items as the list holds -/
theorem decodeMany_exact (n : Nat) (encode : α → List UInt8) (decode : List UInt8 → Option (α × List UInt8))
    (roundtrip : ∀ item rest, decode (encode item ++ rest) = some (item, rest))
    (items : Exact n α) (rest : List UInt8) :
    decodeMany decode n (encodeMany encode items.val ++ rest) = some (items.val, rest) := by
  have counted := decodeMany_encodeMany encode decode roundtrip items.val rest
  rw [items.length_eq] at counted
  exact counted

/-- Binding a known value feeds it straight on: the one step a decoder's round trip takes per field.
    Stated on the monadic bind the do notation produces, so no pass over the decoder is needed first -/
theorem some_bind (a : α) (f : α → Option β) : (some a >>= f) = f a :=
  rfl

/-- Bytes to the end of a frame, at most `most` of them, so the frame's length prefix always fits -/
abbrev Capped (most : Nat) := { bytes : List UInt8 // bytes.length ≤ most }

theorem Capped.length_le (capped : Capped most) : capped.val.length ≤ most :=
  capped.property

/-- A count written from a bounded list reads that list back: the count fits its bytes, so the
    decoder reads exactly as many items as were written -/
theorem decodeMany_bounded (n : Nat) (encode : α → List UInt8) (decode : List UInt8 → Option (α × List UInt8))
    (roundtrip : ∀ item rest, decode (encode item ++ rest) = some (item, rest))
    (items : Bounded n α) (rest : List UInt8) :
    decodeMany decode (BitVec.ofNat (8 * n) items.val.length).toNat (encodeMany encode items.val ++ rest)
      = some (items.val, rest) := by
  have fits : items.val.length < 2 ^ (8 * n) := by
    rw [Nat.pow_mul]
    exact items.length_lt
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits, decodeMany_encodeMany encode decode roundtrip]

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

/-- Items read from the next `size` bytes, to the end of them, and what follows those bytes -/
def decodeSized (item : List UInt8 → Option (α × List UInt8)) (size : Nat) (bytes : List UInt8) : Option (List α × List UInt8) :=
  if size ≤ bytes.length then do
    let items ← decodeAll item size (bytes.take size)
    pure (items, bytes.drop size)
  else none

/-- Items written back to back under a length holding their bytes read back, with what followed -/
theorem decodeSized_encodeMany (n : Nat) (encode : α → List UInt8) (decode : List UInt8 → Option (α × List UInt8))
    (roundtrip : ∀ item rest, decode (encode item ++ rest) = some (item, rest))
    (nonempty : ∀ item, (encode item).length > 0)
    (items : Sized n encode) (rest : List UInt8) :
    decodeSized decode (BitVec.ofNat (8 * n) (encodeMany encode items.val).length).toNat (encodeMany encode items.val ++ rest)
      = some (items.val, rest) := by
  have fits : (encodeMany encode items.val).length < 2 ^ (8 * n) := by
    rw [Nat.pow_mul]
    exact items.length_lt
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits]
  unfold decodeSized
  rw [List.take_left, List.drop_left,
    decodeAll_encodeMany encode decode roundtrip nonempty items.val _ (encodeMany_length_ge encode nonempty items.val)]
  simp [List.length_append]

/-- What may close a message: written when there, nothing when not -/
def encodeTail (encode : α → List UInt8) : Option α → List UInt8
  | none => []
  | some item => encode item

/-- What may close a message: read when bytes remain and must take them all, absent when none do -/
def decodeTail (read : List UInt8 → Option (α × List UInt8)) : List UInt8 → Option (Option α)
  | [] => some none
  | bytes => (read bytes).bind fun (item, rest) => if rest.isEmpty then some (some item) else none

/-- A closing item written back, or nothing, reads back as it was -/
theorem decodeTail_encodeTail (encode : α → List UInt8) (read : List UInt8 → Option (α × List UInt8))
    (roundtrip : ∀ item rest, read (encode item ++ rest) = some (item, rest))
    (nonempty : ∀ item, (encode item).length > 0)
    (tail : Option α) :
    decodeTail read (encodeTail encode tail) = some tail := by
  cases tail with
  | none => rfl
  | some item =>
    have long := nonempty item
    obtain ⟨byte, rest, spelled⟩ : ∃ byte rest, encode item = byte :: rest := by
      cases h : encode item with
      | nil => rw [h] at long; simp at long
      | cons byte rest => exact ⟨byte, rest, rfl⟩
    have step := roundtrip item []
    rw [List.append_nil, spelled] at step
    simp [encodeTail, spelled, decodeTail, step]

/-! ## Framing -/

/-- A length prefix of `n` big endian bytes holding the body's length plus `offset`, then the body.
    The round trip lemmas take their facts at the one message framed, so a body decoder handed the
    fields read ahead of the prefix (a protocol id, flags) qualifies: it need only read back that
    message, not every message -/
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
    (item : α)
    (roundtrip : ∀ rest, decode (encode item ++ rest) = some (item, rest))
    (fits : (encode item).length + offset < 256 ^ n)
    (rest : List UInt8) :
    decodeFramed n offset decode (encodeFramed n offset encode item ++ rest) = some (item, rest) := by
  have bound : (encode item).length + offset < 2 ^ (8 * n) := by
    rw [Nat.pow_mul]
    exact fits
  have whole := roundtrip []
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
    (item : α)
    (roundtrip : ∀ rest, decode (encode item ++ rest) = some (item, rest))
    (fits : (encode item).length + offset < 256 ^ n)
    (rest : List UInt8) :
    decodeFramedLE n offset decode (encodeFramedLE n offset encode item ++ rest) = some (item, rest) := by
  have bound : (encode item).length + offset < 2 ^ (8 * n) := by
    rw [Nat.pow_mul]
    exact fits
  have whole := roundtrip []
  rw [List.append_nil] at whole
  unfold decodeFramedLE encodeFramedLE
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE]
  simp only [Bind.bind, Option.bind_some, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt bound, Nat.add_sub_cancel, take?_append rfl]
  simp [whole, guard]

theorem encodeFramedLE_length (n offset : Nat) (encode : α → List UInt8) (item : α) :
    (encodeFramedLE n offset encode item).length = n + (encode item).length := by
  simp [encodeFramedLE]

/-- Read the prefix, take the bytes it counts, and decode them as a body that runs to their end -/
def decodeFramedAll (n offset : Nat) (decode : List UInt8 → Option α) (bytes : List UInt8) :
    Option (α × List UInt8) := do
  let (length, bytes) ← decodeUInt n bytes
  let (body, rest) ← take? (length.toNat - offset) bytes
  let item ← decode body
  pure (item, rest)

theorem decodeFramedAll_encodeFramed (n offset : Nat) (encode : α → List UInt8)
    (decode : List UInt8 → Option α)
    (item : α)
    (whole : decode (encode item) = some item)
    (fits : (encode item).length + offset < 256 ^ n)
    (rest : List UInt8) :
    decodeFramedAll n offset decode (encodeFramed n offset encode item ++ rest) = some (item, rest) := by
  have bound : (encode item).length + offset < 2 ^ (8 * n) := by
    rw [Nat.pow_mul]
    exact fits
  unfold decodeFramedAll encodeFramed
  rw [List.append_assoc, decodeUInt_encodeUInt]
  simp only [Bind.bind, Option.bind_some, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt bound, Nat.add_sub_cancel, take?_append rfl]
  simp [whole]

def decodeFramedAllLE (n offset : Nat) (decode : List UInt8 → Option α) (bytes : List UInt8) :
    Option (α × List UInt8) := do
  let (length, bytes) ← decodeUIntLE n bytes
  let (body, rest) ← take? (length.toNat - offset) bytes
  let item ← decode body
  pure (item, rest)

theorem decodeFramedAllLE_encodeFramedLE (n offset : Nat) (encode : α → List UInt8)
    (decode : List UInt8 → Option α)
    (item : α)
    (whole : decode (encode item) = some item)
    (fits : (encode item).length + offset < 256 ^ n)
    (rest : List UInt8) :
    decodeFramedAllLE n offset decode (encodeFramedLE n offset encode item ++ rest) = some (item, rest) := by
  have bound : (encode item).length + offset < 2 ^ (8 * n) := by
    rw [Nat.pow_mul]
    exact fits
  unfold decodeFramedAllLE encodeFramedLE
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE]
  simp only [Bind.bind, Option.bind_some, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt bound, Nat.add_sub_cancel, take?_append rfl]
  simp [whole]

/-! ## Fitting bodies -/

/-- A body with the proof its encoding fits its frame's length prefix. Where no bound of the fields
    fits the prefix (groups counted in two bytes under a two byte length), every message carries the
    fit instead, and the frame proof uses that -/
abbrev Fitting (encode : α → List UInt8) (offset limit : Nat) := { item : α // (encode item).length + offset < limit }

instance [DecidableEq α] {encode : α → List UInt8} : DecidableEq (Fitting encode offset limit) :=
  inferInstanceAs (DecidableEq { item : α // (encode item).length + offset < limit })

instance [Repr α] {encode : α → List UInt8} : Repr (Fitting encode offset limit) where
  reprPrec fitting precedence := reprPrec fitting.val precedence

theorem Fitting.fits {encode : α → List UInt8} (fitting : Fitting encode offset limit) :
    (encode fitting.val).length + offset < limit :=
  fitting.property

/-- Read the frame and its body, and keep the body with the fit the prefix showed -/
def decodeFitting (n offset : Nat) (encode : α → List UInt8) (decode : List UInt8 → Option (α × List UInt8))
    (bytes : List UInt8) : Option (Fitting encode offset (256 ^ n) × List UInt8) := do
  let (item, rest) ← decodeFramed n offset decode bytes
  if fits : (encode item).length + offset < 256 ^ n then pure (⟨item, fits⟩, rest) else none

theorem decodeFitting_encodeFramed (n offset : Nat) (encode : α → List UInt8)
    (decode : List UInt8 → Option (α × List UInt8))
    (item : Fitting encode offset (256 ^ n))
    (roundtrip : ∀ rest, decode (encode item.val ++ rest) = some (item.val, rest))
    (rest : List UInt8) :
    decodeFitting n offset encode decode (encodeFramed n offset encode item.val ++ rest) = some (item, rest) := by
  unfold decodeFitting
  rw [decodeFramed_encodeFramed n offset encode decode item.val roundtrip item.fits, some_bind]
  dsimp only
  rw [dite_eq_left item.fits]
  rfl

def decodeFittingLE (n offset : Nat) (encode : α → List UInt8) (decode : List UInt8 → Option (α × List UInt8))
    (bytes : List UInt8) : Option (Fitting encode offset (256 ^ n) × List UInt8) := do
  let (item, rest) ← decodeFramedLE n offset decode bytes
  if fits : (encode item).length + offset < 256 ^ n then pure (⟨item, fits⟩, rest) else none

theorem decodeFittingLE_encodeFramedLE (n offset : Nat) (encode : α → List UInt8)
    (decode : List UInt8 → Option (α × List UInt8))
    (item : Fitting encode offset (256 ^ n))
    (roundtrip : ∀ rest, decode (encode item.val ++ rest) = some (item.val, rest))
    (rest : List UInt8) :
    decodeFittingLE n offset encode decode (encodeFramedLE n offset encode item.val ++ rest) = some (item, rest) := by
  unfold decodeFittingLE
  rw [decodeFramedLE_encodeFramedLE n offset encode decode item.val roundtrip item.fits, some_bind]
  dsimp only
  rw [dite_eq_left item.fits]
  rfl

/-- The same for a body that runs to the end of its frame -/
def decodeFittingAll (n offset : Nat) (encode : α → List UInt8) (decode : List UInt8 → Option α)
    (bytes : List UInt8) : Option (Fitting encode offset (256 ^ n) × List UInt8) := do
  let (item, rest) ← decodeFramedAll n offset decode bytes
  if fits : (encode item).length + offset < 256 ^ n then pure (⟨item, fits⟩, rest) else none

theorem decodeFittingAll_encodeFramed (n offset : Nat) (encode : α → List UInt8)
    (decode : List UInt8 → Option α)
    (item : Fitting encode offset (256 ^ n))
    (whole : decode (encode item.val) = some item.val)
    (rest : List UInt8) :
    decodeFittingAll n offset encode decode (encodeFramed n offset encode item.val ++ rest) = some (item, rest) := by
  unfold decodeFittingAll
  rw [decodeFramedAll_encodeFramed n offset encode decode item.val whole item.fits, some_bind]
  dsimp only
  rw [dite_eq_left item.fits]
  rfl

def decodeFittingAllLE (n offset : Nat) (encode : α → List UInt8) (decode : List UInt8 → Option α)
    (bytes : List UInt8) : Option (Fitting encode offset (256 ^ n) × List UInt8) := do
  let (item, rest) ← decodeFramedAllLE n offset decode bytes
  if fits : (encode item).length + offset < 256 ^ n then pure (⟨item, fits⟩, rest) else none

theorem decodeFittingAllLE_encodeFramedLE (n offset : Nat) (encode : α → List UInt8)
    (decode : List UInt8 → Option α)
    (item : Fitting encode offset (256 ^ n))
    (whole : decode (encode item.val) = some item.val)
    (rest : List UInt8) :
    decodeFittingAllLE n offset encode decode (encodeFramedLE n offset encode item.val ++ rest) = some (item, rest) := by
  unfold decodeFittingAllLE
  rw [decodeFramedAllLE_encodeFramedLE n offset encode decode item.val whole item.fits, some_bind]
  dsimp only
  rw [dite_eq_left item.fits]
  rfl

end Omi