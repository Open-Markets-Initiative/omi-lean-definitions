import Wire

/-!
# The London Metal Exchange LMEsource ReferencePrices Refresh v4.18

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.LmeLmeselectReferencepricessnapshotLmesourceV418

/-- Reference Price Category: one byte code -/
def ReferencePriceCategory.codes : List UInt8 :=
  [0x49, 0x50]

inductive ReferencePriceCategory where
  | instrument -- Instrument
  | product -- Product
  | unlisted (byte : { byte : UInt8 // byte ∉ ReferencePriceCategory.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ReferencePriceCategory

def toByte : ReferencePriceCategory → UInt8
  | .instrument => 0x49
  | .product => 0x50
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ReferencePriceCategory :=
  if byte = 0x49 then .instrument
  else .product

def ofByte (byte : UInt8) : ReferencePriceCategory :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ReferencePriceCategory) : ofByte value.toByte = value := by
  cases value with
  | instrument => decide
  | product => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ReferencePriceCategory) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ReferencePriceCategory × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ReferencePriceCategory) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : ReferencePriceCategory) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : ReferencePriceCategory) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ReferencePriceCategory

/-- Fx Rate Category: one byte code -/
def FxRateCategory.codes : List UInt8 :=
  [0x45, 0x43]

inductive FxRateCategory where
  | exchange -- Exchange
  | closing -- Closing
  | unlisted (byte : { byte : UInt8 // byte ∉ FxRateCategory.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace FxRateCategory

def toByte : FxRateCategory → UInt8
  | .exchange => 0x45
  | .closing => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : FxRateCategory :=
  if byte = 0x45 then .exchange
  else .closing

def ofByte (byte : UInt8) : FxRateCategory :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : FxRateCategory) : ofByte value.toByte = value := by
  cases value with
  | exchange => decide
  | closing => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : FxRateCategory) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (FxRateCategory × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : FxRateCategory) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : FxRateCategory) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : FxRateCategory) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end FxRateCategory

/-- Surface Domain: one byte code -/
def SurfaceDomain.codes : List UInt8 :=
  [0x53, 0x44]

inductive SurfaceDomain where
  | strike -- Strike
  | delta -- Delta
  | unlisted (byte : { byte : UInt8 // byte ∉ SurfaceDomain.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SurfaceDomain

def toByte : SurfaceDomain → UInt8
  | .strike => 0x53
  | .delta => 0x44
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SurfaceDomain :=
  if byte = 0x53 then .strike
  else .delta

def ofByte (byte : UInt8) : SurfaceDomain :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SurfaceDomain) : ofByte value.toByte = value := by
  cases value with
  | strike => decide
  | delta => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SurfaceDomain) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SurfaceDomain × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SurfaceDomain) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : SurfaceDomain) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : SurfaceDomain) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SurfaceDomain

/-- Sequence Reset Message: 4 bytes -/
structure SequenceResetMessage where
  newSeqNo : BitVec 32
  deriving DecidableEq, Repr

namespace SequenceResetMessage

def encode (message : SequenceResetMessage) : List UInt8 :=
  encodeUIntLE 4 message.newSeqNo

def decode (bytes : List UInt8) : Option (SequenceResetMessage × List UInt8) := do
  let (newSeqNo, bytes) ← decodeUIntLE 4 bytes
  pure ({ newSeqNo }, bytes)

@[simp] theorem encode_length (message : SequenceResetMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : SequenceResetMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SequenceResetMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SequenceResetMessage

/-- Reference Price Message: 94 bytes -/
structure ReferencePriceMessage where
  timeOfEvent : BitVec 64
  referencePriceCategory : ReferencePriceCategory
  referencePriceType : Alpha 32
  priceStatus : Alpha 12
  businessDate : BitVec 32
  instrumentId : BitVec 64
  productCode : Alpha 2
  currencyCode : Alpha 3
  bid : BitVec 64
  price : BitVec 64
  ask : BitVec 64
  deriving DecidableEq, Repr

namespace ReferencePriceMessage

def encode (message : ReferencePriceMessage) : List UInt8 :=
  encodeUIntLE 8 message.timeOfEvent
    ++ (ReferencePriceCategory.encode message.referencePriceCategory
    ++ (Alpha.encode message.referencePriceType
    ++ (Alpha.encode message.priceStatus
    ++ (encodeUIntLE 4 message.businessDate
    ++ (encodeUIntLE 8 message.instrumentId
    ++ (Alpha.encode message.productCode
    ++ (Alpha.encode message.currencyCode
    ++ (encodeUIntLE 8 message.bid
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 8 message.ask))))))))))

def decode (bytes : List UInt8) : Option (ReferencePriceMessage × List UInt8) := do
  let (timeOfEvent, bytes) ← decodeUIntLE 8 bytes
  let (referencePriceCategory, bytes) ← ReferencePriceCategory.decode bytes
  let (referencePriceType, bytes) ← Alpha.decode 32 bytes
  let (priceStatus, bytes) ← Alpha.decode 12 bytes
  let (businessDate, bytes) ← decodeUIntLE 4 bytes
  let (instrumentId, bytes) ← decodeUIntLE 8 bytes
  let (productCode, bytes) ← Alpha.decode 2 bytes
  let (currencyCode, bytes) ← Alpha.decode 3 bytes
  let (bid, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (ask, bytes) ← decodeUIntLE 8 bytes
  pure ({ timeOfEvent, referencePriceCategory, referencePriceType, priceStatus, businessDate, instrumentId, productCode, currencyCode, bid, price, ask }, bytes)

@[simp] theorem encode_length (message : ReferencePriceMessage) : (encode message).length = 94 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, ReferencePriceCategory.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : ReferencePriceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ReferencePriceMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, ReferencePriceCategory.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end ReferencePriceMessage

/-- Curve Prices: 28 bytes -/
structure CurvePrices where
  price : BitVec 64
  promptDate1 : BitVec 32
  promptDateLabel1 : Alpha 6
  promptDate2 : BitVec 32
  promptDateLabel2 : Alpha 6
  deriving DecidableEq, Repr

namespace CurvePrices

def encode (message : CurvePrices) : List UInt8 :=
  encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.promptDate1
    ++ (Alpha.encode message.promptDateLabel1
    ++ (encodeUIntLE 4 message.promptDate2
    ++ (Alpha.encode message.promptDateLabel2))))

def decode (bytes : List UInt8) : Option (CurvePrices × List UInt8) := do
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (promptDate1, bytes) ← decodeUIntLE 4 bytes
  let (promptDateLabel1, bytes) ← Alpha.decode 6 bytes
  let (promptDate2, bytes) ← decodeUIntLE 4 bytes
  let (promptDateLabel2, bytes) ← Alpha.decode 6 bytes
  pure ({ price, promptDate1, promptDateLabel1, promptDate2, promptDateLabel2 }, bytes)

@[simp] theorem encode_length (message : CurvePrices) : (encode message).length = 28 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : CurvePrices) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CurvePrices) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end CurvePrices

/-- Reference Forward Curve Price Message -/
structure ReferenceForwardCurvePriceMessage where
  timeOfEvent : BitVec 64
  businessDate : BitVec 32
  productCode : Alpha 2
  priceStatus : Alpha 12
  currencyCode : Alpha 3
  remainingRecords : BitVec 16
  curvePrices : Bounded 2 CurvePrices
  deriving DecidableEq, Repr

namespace ReferenceForwardCurvePriceMessage

def encode (message : ReferenceForwardCurvePriceMessage) : List UInt8 :=
  encodeUIntLE 8 message.timeOfEvent
    ++ (encodeUIntLE 4 message.businessDate
    ++ (Alpha.encode message.productCode
    ++ (Alpha.encode message.priceStatus
    ++ (Alpha.encode message.currencyCode
    ++ (encodeUIntLE 2 message.remainingRecords
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.curvePrices.val.length)
    ++ (encodeMany CurvePrices.encode message.curvePrices.val)))))))

def decode (bytes : List UInt8) : Option (ReferenceForwardCurvePriceMessage × List UInt8) := do
  let (timeOfEvent, bytes) ← decodeUIntLE 8 bytes
  let (businessDate, bytes) ← decodeUIntLE 4 bytes
  let (productCode, bytes) ← Alpha.decode 2 bytes
  let (priceStatus, bytes) ← Alpha.decode 12 bytes
  let (currencyCode, bytes) ← Alpha.decode 3 bytes
  let (remainingRecords, bytes) ← decodeUIntLE 2 bytes
  let (recordCount, bytes) ← decodeUIntLE 2 bytes
  let (curvePrices_, bytes) ← decodeMany CurvePrices.decode recordCount.toNat bytes
  if fits_curvePrices : curvePrices_.length < 256 ^ 2 then
    pure ({ timeOfEvent, businessDate, productCode, priceStatus, currencyCode, remainingRecords, curvePrices := ⟨curvePrices_, fits_curvePrices⟩ }, bytes)
  else none

theorem encode_length_pos (message : ReferenceForwardCurvePriceMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ReferenceForwardCurvePriceMessage) : (encode message).length ≤ 1835013 := by
  have bound_curvePrices := message.curvePrices.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, Alpha.encode_length, encodeMany_length_const CurvePrices.encode 28 CurvePrices.encode_length]
  omega

@[simp] theorem decode_encode (message : ReferenceForwardCurvePriceMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 CurvePrices.encode CurvePrices.decode CurvePrices.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.curvePrices.length_lt]
  rfl

end ReferenceForwardCurvePriceMessage

/-- Reference Fx Rate Message: 25 bytes -/
structure ReferenceFxRateMessage where
  fxRateCategory : FxRateCategory
  fxRateType : Alpha 2
  businessDate : BitVec 32
  maturityDate : BitVec 32
  baseCurrencyCode : Alpha 3
  targetCurrencyCode : Alpha 3
  conversionRate : BitVec 64
  deriving DecidableEq, Repr

namespace ReferenceFxRateMessage

def encode (message : ReferenceFxRateMessage) : List UInt8 :=
  FxRateCategory.encode message.fxRateCategory
    ++ (Alpha.encode message.fxRateType
    ++ (encodeUIntLE 4 message.businessDate
    ++ (encodeUIntLE 4 message.maturityDate
    ++ (Alpha.encode message.baseCurrencyCode
    ++ (Alpha.encode message.targetCurrencyCode
    ++ (encodeUIntLE 8 message.conversionRate))))))

def decode (bytes : List UInt8) : Option (ReferenceFxRateMessage × List UInt8) := do
  let (fxRateCategory, bytes) ← FxRateCategory.decode bytes
  let (fxRateType, bytes) ← Alpha.decode 2 bytes
  let (businessDate, bytes) ← decodeUIntLE 4 bytes
  let (maturityDate, bytes) ← decodeUIntLE 4 bytes
  let (baseCurrencyCode, bytes) ← Alpha.decode 3 bytes
  let (targetCurrencyCode, bytes) ← Alpha.decode 3 bytes
  let (conversionRate, bytes) ← decodeUIntLE 8 bytes
  pure ({ fxRateCategory, fxRateType, businessDate, maturityDate, baseCurrencyCode, targetCurrencyCode, conversionRate }, bytes)

@[simp] theorem encode_length (message : ReferenceFxRateMessage) : (encode message).length = 25 := by
  unfold encode
  simp only [List.length_append, FxRateCategory.encode_length, Alpha.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : ReferenceFxRateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ReferenceFxRateMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, FxRateCategory.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end ReferenceFxRateMessage

/-- Volatility Points: 50 bytes -/
structure VolatilityPoints where
  surfaceDomain : SurfaceDomain
  delta : BitVec 64
  strikePrice : BitVec 64
  atm : BitVec 8
  callVolatility : BitVec 64
  putVolatility : BitVec 64
  callPremium : BitVec 64
  putPremium : BitVec 64
  deriving DecidableEq, Repr

namespace VolatilityPoints

def encode (message : VolatilityPoints) : List UInt8 :=
  SurfaceDomain.encode message.surfaceDomain
    ++ (encodeUIntLE 8 message.delta
    ++ (encodeUIntLE 8 message.strikePrice
    ++ (encodeUInt 1 message.atm
    ++ (encodeUIntLE 8 message.callVolatility
    ++ (encodeUIntLE 8 message.putVolatility
    ++ (encodeUIntLE 8 message.callPremium
    ++ (encodeUIntLE 8 message.putPremium)))))))

def decode (bytes : List UInt8) : Option (VolatilityPoints × List UInt8) := do
  let (surfaceDomain, bytes) ← SurfaceDomain.decode bytes
  let (delta, bytes) ← decodeUIntLE 8 bytes
  let (strikePrice, bytes) ← decodeUIntLE 8 bytes
  let (atm, bytes) ← decodeUInt 1 bytes
  let (callVolatility, bytes) ← decodeUIntLE 8 bytes
  let (putVolatility, bytes) ← decodeUIntLE 8 bytes
  let (callPremium, bytes) ← decodeUIntLE 8 bytes
  let (putPremium, bytes) ← decodeUIntLE 8 bytes
  pure ({ surfaceDomain, delta, strikePrice, atm, callVolatility, putVolatility, callPremium, putPremium }, bytes)

@[simp] theorem encode_length (message : VolatilityPoints) : (encode message).length = 50 := by
  unfold encode
  simp only [List.length_append, SurfaceDomain.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : VolatilityPoints) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : VolatilityPoints) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, SurfaceDomain.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end VolatilityPoints

/-- Reference Volatility Price Message -/
structure ReferenceVolatilityPriceMessage where
  timeOfEvent : BitVec 64
  businessDate : BitVec 32
  contractCode : Alpha 12
  expiryDate : BitVec 32
  remainingRecords : BitVec 16
  volatilityPoints : Bounded 2 VolatilityPoints
  deriving DecidableEq, Repr

namespace ReferenceVolatilityPriceMessage

def encode (message : ReferenceVolatilityPriceMessage) : List UInt8 :=
  encodeUIntLE 8 message.timeOfEvent
    ++ (encodeUIntLE 4 message.businessDate
    ++ (Alpha.encode message.contractCode
    ++ (encodeUIntLE 4 message.expiryDate
    ++ (encodeUIntLE 2 message.remainingRecords
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.volatilityPoints.val.length)
    ++ (encodeMany VolatilityPoints.encode message.volatilityPoints.val))))))

def decode (bytes : List UInt8) : Option (ReferenceVolatilityPriceMessage × List UInt8) := do
  let (timeOfEvent, bytes) ← decodeUIntLE 8 bytes
  let (businessDate, bytes) ← decodeUIntLE 4 bytes
  let (contractCode, bytes) ← Alpha.decode 12 bytes
  let (expiryDate, bytes) ← decodeUIntLE 4 bytes
  let (remainingRecords, bytes) ← decodeUIntLE 2 bytes
  let (recordCount, bytes) ← decodeUIntLE 2 bytes
  let (volatilityPoints_, bytes) ← decodeMany VolatilityPoints.decode recordCount.toNat bytes
  if fits_volatilityPoints : volatilityPoints_.length < 256 ^ 2 then
    pure ({ timeOfEvent, businessDate, contractCode, expiryDate, remainingRecords, volatilityPoints := ⟨volatilityPoints_, fits_volatilityPoints⟩ }, bytes)
  else none

theorem encode_length_pos (message : ReferenceVolatilityPriceMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ReferenceVolatilityPriceMessage) : (encode message).length ≤ 3276782 := by
  have bound_volatilityPoints := message.volatilityPoints.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, Alpha.encode_length, encodeMany_length_const VolatilityPoints.encode 50 VolatilityPoints.encode_length]
  omega

@[simp] theorem decode_encode (message : ReferenceVolatilityPriceMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 VolatilityPoints.encode VolatilityPoints.decode VolatilityPoints.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.volatilityPoints.length_lt]
  rfl

end ReferenceVolatilityPriceMessage

/-- Refresh Complete Message: 4 bytes -/
structure RefreshCompleteMessage where
  lastSeqNum : BitVec 32
  deriving DecidableEq, Repr

namespace RefreshCompleteMessage

def encode (message : RefreshCompleteMessage) : List UInt8 :=
  encodeUIntLE 4 message.lastSeqNum

def decode (bytes : List UInt8) : Option (RefreshCompleteMessage × List UInt8) := do
  let (lastSeqNum, bytes) ← decodeUIntLE 4 bytes
  pure ({ lastSeqNum }, bytes)

@[simp] theorem encode_length (message : RefreshCompleteMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : RefreshCompleteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RefreshCompleteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end RefreshCompleteMessage

/-- Any Payload, selected by Msg Type -/
inductive Payload where
  | sequenceResetMessage (message : SequenceResetMessage) -- 100
  | referencePriceMessage (message : ReferencePriceMessage) -- 401
  | referenceForwardCurvePriceMessage (message : ReferenceForwardCurvePriceMessage) -- 402
  | referenceFxRateMessage (message : ReferenceFxRateMessage) -- 403
  | referenceVolatilityPriceMessage (message : ReferenceVolatilityPriceMessage) -- 404
  | refreshCompleteMessage (message : RefreshCompleteMessage) -- 203
  deriving DecidableEq, Repr

namespace Payload

/-- The Msg Type each message is sent under -/
def tag : Payload → BitVec 16
  | .sequenceResetMessage _ => 100
  | .referencePriceMessage _ => 401
  | .referenceForwardCurvePriceMessage _ => 402
  | .referenceFxRateMessage _ => 403
  | .referenceVolatilityPriceMessage _ => 404
  | .refreshCompleteMessage _ => 203

def encode : Payload → List UInt8
  | .sequenceResetMessage message => SequenceResetMessage.encode message
  | .referencePriceMessage message => ReferencePriceMessage.encode message
  | .referenceForwardCurvePriceMessage message => ReferenceForwardCurvePriceMessage.encode message
  | .referenceFxRateMessage message => ReferenceFxRateMessage.encode message
  | .referenceVolatilityPriceMessage message => ReferenceVolatilityPriceMessage.encode message
  | .refreshCompleteMessage message => RefreshCompleteMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 3276782 := by
  cases message with
  | sequenceResetMessage inner =>
    simp only [encode, SequenceResetMessage.encode_length]
    omega
  | referencePriceMessage inner =>
    simp only [encode, ReferencePriceMessage.encode_length]
    omega
  | referenceForwardCurvePriceMessage inner =>
    have bound_inner := ReferenceForwardCurvePriceMessage.encode_length_le inner
    simp only [encode]
    omega
  | referenceFxRateMessage inner =>
    simp only [encode, ReferenceFxRateMessage.encode_length]
    omega
  | referenceVolatilityPriceMessage inner =>
    have bound_inner := ReferenceVolatilityPriceMessage.encode_length_le inner
    simp only [encode]
    omega
  | refreshCompleteMessage inner =>
    simp only [encode, RefreshCompleteMessage.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 100 then (SequenceResetMessage.decode bytes).map fun (message, rest) => (.sequenceResetMessage message, rest)
  else if tag = 401 then (ReferencePriceMessage.decode bytes).map fun (message, rest) => (.referencePriceMessage message, rest)
  else if tag = 402 then (ReferenceForwardCurvePriceMessage.decode bytes).map fun (message, rest) => (.referenceForwardCurvePriceMessage message, rest)
  else if tag = 403 then (ReferenceFxRateMessage.decode bytes).map fun (message, rest) => (.referenceFxRateMessage message, rest)
  else if tag = 404 then (ReferenceVolatilityPriceMessage.decode bytes).map fun (message, rest) => (.referenceVolatilityPriceMessage message, rest)
  else if tag = 203 then (RefreshCompleteMessage.decode bytes).map fun (message, rest) => (.refreshCompleteMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Message -/
structure Message where
  msgSize : BitVec 16
  payload : Payload
  deriving DecidableEq, Repr

namespace Message

def encode (message : Message) : List UInt8 :=
  encodeUIntLE 2 message.msgSize
    ++ (encodeUIntLE 2 (Payload.tag message.payload)
    ++ (Payload.encode message.payload))

def decode (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (msgSize, bytes) ← decodeUIntLE 2 bytes
  let (msgType, bytes) ← decodeUIntLE 2 bytes
  let (payload, bytes) ← Payload.decode msgType bytes
  pure ({ msgSize, payload }, bytes)

theorem encode_length_pos (message : Message) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : Message) : (encode message).length ≤ 3276786 := by
  unfold encode
  cases message.payload with
  | sequenceResetMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, SequenceResetMessage.encode_length]
    omega
  | referencePriceMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, ReferencePriceMessage.encode_length]
    omega
  | referenceForwardCurvePriceMessage inner =>
    have bound_inner := ReferenceForwardCurvePriceMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | referenceFxRateMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, ReferenceFxRateMessage.encode_length]
    omega
  | referenceVolatilityPriceMessage inner =>
    have bound_inner := ReferenceVolatilityPriceMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | refreshCompleteMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, RefreshCompleteMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Payload.decode_encode, some_bind]
  rfl

end Message

/-- Packet -/
structure Packet where
  pktSize : BitVec 16
  filler : Alpha 1
  seqNum : BitVec 32
  sendTime : BitVec 64
  message : Bounded 1 Message
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeUIntLE 2 message.pktSize
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.message.val.length)
    ++ (Alpha.encode message.filler
    ++ (encodeUIntLE 4 message.seqNum
    ++ (encodeUIntLE 8 message.sendTime
    ++ (encodeMany Message.encode message.message.val)))))

def decode (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (pktSize, bytes) ← decodeUIntLE 2 bytes
  let (msgCount, bytes) ← decodeUInt 1 bytes
  let (filler, bytes) ← Alpha.decode 1 bytes
  let (seqNum, bytes) ← decodeUIntLE 4 bytes
  let (sendTime, bytes) ← decodeUIntLE 8 bytes
  let (message_, bytes) ← decodeMany Message.decode msgCount.toNat bytes
  if fits_message : message_.length < 256 ^ 1 then
    pure ({ pktSize, filler, seqNum, sendTime, message := ⟨message_, fits_message⟩ }, bytes)
  else none

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : Packet) : (encode message).length ≤ 835580446 := by
  have bound_message := message.message.length_lt
  have bound_message_items := encodeMany_length_le Message.encode 3276786 Message.encode_length_le message.message.val
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]
  omega

@[simp] theorem decode_encode (message : Packet) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 Message.encode Message.decode Message.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.message.length_lt]
  rfl

end Packet

end Omi.LmeLmeselectReferencepricessnapshotLmesourceV418
