import Wire

/-!
# TMX Group Global Fx Feed v1.0

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.TmxTsxGlobalfxGfxV10

/-- Tier Status: one byte code -/
def TierStatus.codes : List UInt8 :=
  [0x52, 0x5A]

inductive TierStatus where
  | validReferencePrice -- Valid Reference Price
  | priceNotAvailable -- Price Not Available
  | unlisted (byte : { byte : UInt8 // byte ∉ TierStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TierStatus

def toByte : TierStatus → UInt8
  | .validReferencePrice => 0x52
  | .priceNotAvailable => 0x5A
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TierStatus :=
  if byte = 0x52 then .validReferencePrice
  else .priceNotAvailable

def ofByte (byte : UInt8) : TierStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TierStatus) : ofByte value.toByte = value := by
  cases value with
  | validReferencePrice => decide
  | priceNotAvailable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TierStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TierStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TierStatus) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TierStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TierStatus

/-- Price Terms: one byte code -/
def PriceTerms.codes : List UInt8 :=
  [0x44, 0x49]

inductive PriceTerms where
  | directTerms -- Direct Terms
  | invertedTerms -- Inverted Terms
  | unlisted (byte : { byte : UInt8 // byte ∉ PriceTerms.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PriceTerms

def toByte : PriceTerms → UInt8
  | .directTerms => 0x44
  | .invertedTerms => 0x49
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PriceTerms :=
  if byte = 0x44 then .directTerms
  else .invertedTerms

def ofByte (byte : UInt8) : PriceTerms :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PriceTerms) : ofByte value.toByte = value := by
  cases value with
  | directTerms => decide
  | invertedTerms => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PriceTerms) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PriceTerms × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PriceTerms) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : PriceTerms) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PriceTerms

/-- Bid Price: 5 bytes -/
structure BidPrice where
  bidPriceMantissa : BitVec 32
  bidPriceExponent : BitVec 8
  deriving DecidableEq, Repr

namespace BidPrice

def encode (message : BidPrice) : List UInt8 :=
  encodeUInt 4 message.bidPriceMantissa
    ++ (encodeUInt 1 message.bidPriceExponent)

def decode (bytes : List UInt8) : Option (BidPrice × List UInt8) := do
  let (bidPriceMantissa, bytes) ← decodeUInt 4 bytes
  let (bidPriceExponent, bytes) ← decodeUInt 1 bytes
  pure ({ bidPriceMantissa, bidPriceExponent }, bytes)

@[simp] theorem encode_length (message : BidPrice) : (encode message).length = 5 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : BidPrice) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BidPrice) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end BidPrice

/-- Offer Price: 5 bytes -/
structure OfferPrice where
  offerPriceMantissa : BitVec 32
  offerPriceExponent : BitVec 8
  deriving DecidableEq, Repr

namespace OfferPrice

def encode (message : OfferPrice) : List UInt8 :=
  encodeUInt 4 message.offerPriceMantissa
    ++ (encodeUInt 1 message.offerPriceExponent)

def decode (bytes : List UInt8) : Option (OfferPrice × List UInt8) := do
  let (offerPriceMantissa, bytes) ← decodeUInt 4 bytes
  let (offerPriceExponent, bytes) ← decodeUInt 1 bytes
  pure ({ offerPriceMantissa, offerPriceExponent }, bytes)

@[simp] theorem encode_length (message : OfferPrice) : (encode message).length = 5 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : OfferPrice) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OfferPrice) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OfferPrice

/-- Size Tier: 16 bytes -/
structure SizeTier where
  tierStatus : TierStatus
  tierSize : BitVec 32
  priceTerms : PriceTerms
  bidPrice : BidPrice
  offerPrice : OfferPrice
  deriving DecidableEq, Repr

namespace SizeTier

def encode (message : SizeTier) : List UInt8 :=
  TierStatus.encode message.tierStatus
    ++ (encodeUInt 4 message.tierSize
    ++ (PriceTerms.encode message.priceTerms
    ++ (BidPrice.encode message.bidPrice
    ++ (OfferPrice.encode message.offerPrice))))

def decode (bytes : List UInt8) : Option (SizeTier × List UInt8) := do
  let (tierStatus, bytes) ← TierStatus.decode bytes
  let (tierSize, bytes) ← decodeUInt 4 bytes
  let (priceTerms, bytes) ← PriceTerms.decode bytes
  let (bidPrice, bytes) ← BidPrice.decode bytes
  let (offerPrice, bytes) ← OfferPrice.decode bytes
  pure ({ tierStatus, tierSize, priceTerms, bidPrice, offerPrice }, bytes)

@[simp] theorem encode_length (message : SizeTier) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, TierStatus.encode_length, encodeUInt_length, PriceTerms.encode_length, BidPrice.encode_length, OfferPrice.encode_length]

theorem encode_length_pos (message : SizeTier) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SizeTier) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, TierStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, PriceTerms.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, BidPrice.decode_encode, some_bind]
  dsimp only
  rw [OfferPrice.decode_encode, some_bind]
  rfl

end SizeTier

/-- Reference Price Fx Spot -/
structure ReferencePriceFxSpot where
  unused1 : Alpha 1
  currency1 : Alpha 3
  currency2 : Alpha 3
  timestamp : BitVec 64
  streamId : BitVec 64
  sequenceNumber : BitVec 32
  validForSeconds : BitVec 16
  unused2 : Alpha 1
  sizeTier : Bounded 1 SizeTier
  deriving DecidableEq, Repr

namespace ReferencePriceFxSpot

def encode (message : ReferencePriceFxSpot) : List UInt8 :=
  Alpha.encode message.unused1
    ++ (Alpha.encode message.currency1
    ++ (Alpha.encode message.currency2
    ++ (encodeUInt 8 message.timestamp
    ++ (encodeUInt 8 message.streamId
    ++ (encodeUInt 4 message.sequenceNumber
    ++ (encodeUInt 2 message.validForSeconds
    ++ (Alpha.encode message.unused2
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.sizeTier.val.length)
    ++ (encodeMany SizeTier.encode message.sizeTier.val)))))))))

def decode (bytes : List UInt8) : Option (ReferencePriceFxSpot × List UInt8) := do
  let (unused1, bytes) ← Alpha.decode 1 bytes
  let (currency1, bytes) ← Alpha.decode 3 bytes
  let (currency2, bytes) ← Alpha.decode 3 bytes
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (streamId, bytes) ← decodeUInt 8 bytes
  let (sequenceNumber, bytes) ← decodeUInt 4 bytes
  let (validForSeconds, bytes) ← decodeUInt 2 bytes
  let (unused2, bytes) ← Alpha.decode 1 bytes
  let (numberOfTiers, bytes) ← decodeUInt 1 bytes
  let (sizeTier_, bytes) ← decodeMany SizeTier.decode numberOfTiers.toNat bytes
  if fits_sizeTier : sizeTier_.length < 256 ^ 1 then
    pure ({ unused1, currency1, currency2, timestamp, streamId, sequenceNumber, validForSeconds, unused2, sizeTier := ⟨sizeTier_, fits_sizeTier⟩ }, bytes)
  else none

theorem encode_length_pos (message : ReferencePriceFxSpot) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ReferencePriceFxSpot) : (encode message).length ≤ 4111 := by
  have bound_sizeTier := message.sizeTier.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, encodeMany_length_const SizeTier.encode 16 SizeTier.encode_length]
  omega

@[simp] theorem decode_encode (message : ReferencePriceFxSpot) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 SizeTier.encode SizeTier.decode SizeTier.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.sizeTier.length_lt]
  rfl

end ReferencePriceFxSpot

/-- Any Datagram Body, selected by Msg Type -/
inductive DatagramBody where
  | referencePriceFxSpot (message : ReferencePriceFxSpot) -- "#" 0x23
  deriving DecidableEq, Repr

namespace DatagramBody

/-- The Msg Type each message is sent under -/
def tag : DatagramBody → BitVec 8
  | .referencePriceFxSpot _ => 35

def encode : DatagramBody → List UInt8
  | .referencePriceFxSpot message => ReferencePriceFxSpot.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : DatagramBody) : (encode message).length ≤ 4111 := by
  cases message with
  | referencePriceFxSpot inner =>
    have bound_inner := ReferencePriceFxSpot.encode_length_le inner
    simp only [encode]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (DatagramBody × List UInt8) :=
  if tag = 35 then (ReferencePriceFxSpot.decode bytes).map fun (message, rest) => (.referencePriceFxSpot message, rest)
  else none

@[simp] theorem decode_encode (message : DatagramBody) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end DatagramBody

/-- Packet -/
structure Packet where
  datagramBody : DatagramBody
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeUInt 1 (DatagramBody.tag message.datagramBody)
    ++ (DatagramBody.encode message.datagramBody)

def decode (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (msgType, bytes) ← decodeUInt 1 bytes
  let (datagramBody, bytes) ← DatagramBody.decode msgType bytes
  pure ({ datagramBody }, bytes)

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : Packet) : (encode message).length ≤ 4112 := by
  unfold encode
  cases message.datagramBody with
  | referencePriceFxSpot inner =>
    have bound_inner := ReferencePriceFxSpot.encode_length_le inner
    simp only [DatagramBody.encode, List.length_append, encodeUInt_length]
    omega

@[simp] theorem decode_encode (message : Packet) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [DatagramBody.decode_encode, some_bind]
  rfl

end Packet

end Omi.TmxTsxGlobalfxGfxV10
