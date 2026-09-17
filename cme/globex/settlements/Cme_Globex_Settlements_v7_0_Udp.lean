import Omi.Wire

/-!
# CME Group Settlements v7.0

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Settl Price Type is a bit field set, proven as its 1 byte integer rather than bit by bit.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.CmeGlobexSettlementsSbeV70Udp

/-- Low Px Ind: one byte code -/
def LowPxInd.codes : List UInt8 :=
  [0x41, 0x42, 0x54]

inductive LowPxInd where
  | ask -- Ask
  | bid -- Bid
  | trade -- Trade
  | unlisted (byte : { byte : UInt8 // byte ∉ LowPxInd.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LowPxInd

def toByte : LowPxInd → UInt8
  | .ask => 0x41
  | .bid => 0x42
  | .trade => 0x54
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LowPxInd :=
  if byte = 0x41 then .ask
  else if byte = 0x42 then .bid
  else .trade

def ofByte (byte : UInt8) : LowPxInd :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LowPxInd) : ofByte value.toByte = value := by
  cases value with
  | ask => decide
  | bid => decide
  | trade => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LowPxInd) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LowPxInd × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LowPxInd) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : LowPxInd) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LowPxInd

/-- High Px Ind: one byte code -/
def HighPxInd.codes : List UInt8 :=
  [0x41, 0x42, 0x54]

inductive HighPxInd where
  | ask -- Ask
  | bid -- Bid
  | trade -- Trade
  | unlisted (byte : { byte : UInt8 // byte ∉ HighPxInd.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace HighPxInd

def toByte : HighPxInd → UInt8
  | .ask => 0x41
  | .bid => 0x42
  | .trade => 0x54
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : HighPxInd :=
  if byte = 0x41 then .ask
  else if byte = 0x42 then .bid
  else .trade

def ofByte (byte : UInt8) : HighPxInd :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : HighPxInd) : ofByte value.toByte = value := by
  cases value with
  | ask => decide
  | bid => decide
  | trade => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : HighPxInd) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (HighPxInd × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : HighPxInd) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : HighPxInd) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end HighPxInd

/-- Binary Packet Header: 12 bytes -/
structure BinaryPacketHeader where
  packetSequenceNumber : BitVec 32
  sendingTime : BitVec 64
  deriving DecidableEq, Repr

namespace BinaryPacketHeader

def encode (message : BinaryPacketHeader) : List UInt8 :=
  encodeUIntLE 4 message.packetSequenceNumber
    ++ encodeUIntLE 8 message.sendingTime

def decode (bytes : List UInt8) : Option (BinaryPacketHeader × List UInt8) := do
  let (packetSequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (sendingTime, bytes) ← decodeUIntLE 8 bytes
  pure ({ packetSequenceNumber, sendingTime }, bytes)

@[simp] theorem encode_length (message : BinaryPacketHeader) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : BinaryPacketHeader) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BinaryPacketHeader) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

end BinaryPacketHeader

/-- Maturity Month Year: 5 bytes -/
structure MaturityMonthYear where
  year : BitVec 16
  month : BitVec 8
  day : BitVec 8
  week : BitVec 8
  deriving DecidableEq, Repr

namespace MaturityMonthYear

def encode (message : MaturityMonthYear) : List UInt8 :=
  encodeUIntLE 2 message.year
    ++ encodeUInt 1 message.month
    ++ encodeUInt 1 message.day
    ++ encodeUInt 1 message.week

def decode (bytes : List UInt8) : Option (MaturityMonthYear × List UInt8) := do
  let (year, bytes) ← decodeUIntLE 2 bytes
  let (month, bytes) ← decodeUInt 1 bytes
  let (day, bytes) ← decodeUInt 1 bytes
  let (week, bytes) ← decodeUInt 1 bytes
  pure ({ year, month, day, week }, bytes)

@[simp] theorem encode_length (message : MaturityMonthYear) : (encode message).length = 5 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : MaturityMonthYear) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MaturityMonthYear) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end MaturityMonthYear

/-- Strike Price: 9 bytes -/
structure StrikePrice where
  mantissa : BitVec 64
  exponent : BitVec 8
  deriving DecidableEq, Repr

namespace StrikePrice

def encode (message : StrikePrice) : List UInt8 :=
  encodeUIntLE 8 message.mantissa
    ++ encodeUInt 1 message.exponent

def decode (bytes : List UInt8) : Option (StrikePrice × List UInt8) := do
  let (mantissa, bytes) ← decodeUIntLE 8 bytes
  let (exponent, bytes) ← decodeUInt 1 bytes
  pure ({ mantissa, exponent }, bytes)

@[simp] theorem encode_length (message : StrikePrice) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : StrikePrice) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StrikePrice) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end StrikePrice

/-- Underlying Maturity Month Year: 5 bytes -/
structure UnderlyingMaturityMonthYear where
  year : BitVec 16
  month : BitVec 8
  day : BitVec 8
  week : BitVec 8
  deriving DecidableEq, Repr

namespace UnderlyingMaturityMonthYear

def encode (message : UnderlyingMaturityMonthYear) : List UInt8 :=
  encodeUIntLE 2 message.year
    ++ encodeUInt 1 message.month
    ++ encodeUInt 1 message.day
    ++ encodeUInt 1 message.week

def decode (bytes : List UInt8) : Option (UnderlyingMaturityMonthYear × List UInt8) := do
  let (year, bytes) ← decodeUIntLE 2 bytes
  let (month, bytes) ← decodeUInt 1 bytes
  let (day, bytes) ← decodeUInt 1 bytes
  let (week, bytes) ← decodeUInt 1 bytes
  pure ({ year, month, day, week }, bytes)

@[simp] theorem encode_length (message : UnderlyingMaturityMonthYear) : (encode message).length = 5 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : UnderlyingMaturityMonthYear) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UnderlyingMaturityMonthYear) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end UnderlyingMaturityMonthYear

/-- Formatted Last Px: 9 bytes -/
structure FormattedLastPx where
  mantissa : BitVec 64
  exponent : BitVec 8
  deriving DecidableEq, Repr

namespace FormattedLastPx

def encode (message : FormattedLastPx) : List UInt8 :=
  encodeUIntLE 8 message.mantissa
    ++ encodeUInt 1 message.exponent

def decode (bytes : List UInt8) : Option (FormattedLastPx × List UInt8) := do
  let (mantissa, bytes) ← decodeUIntLE 8 bytes
  let (exponent, bytes) ← decodeUInt 1 bytes
  pure ({ mantissa, exponent }, bytes)

@[simp] theorem encode_length (message : FormattedLastPx) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : FormattedLastPx) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FormattedLastPx) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end FormattedLastPx

/-- Incremental Refresh Settle Group: 182 bytes -/
structure IncrementalRefreshSettleGroup where
  mdUpdateAction : BitVec 8
  mdEntryType : Alpha 1
  productGuid : BitVec 64
  clearingProductCode : Alpha 12
  securityType : Alpha 6
  securityExchange : Alpha 8
  maturityMonthYear : MaturityMonthYear
  putOrCall : BitVec 8
  strikePrice : StrikePrice
  underlyingProductGuid : BitVec 64
  underlyingClearingProductCode : Alpha 12
  underlyingSecurityType : Alpha 6
  underlyingSecurityExchange : Alpha 8
  underlyingMaturityMonthYear : UnderlyingMaturityMonthYear
  symbol : Alpha 20
  instrumentGuid : BitVec 64
  securityId : BitVec 32
  formattedLastPx : FormattedLastPx
  mdEntryPx : BitVec 64
  settlPriceType : BitVec 8
  tradingReferenceDate : BitVec 16
  mdStatisticDesc : Alpha 40
  deriving DecidableEq, Repr

namespace IncrementalRefreshSettleGroup

def encode (message : IncrementalRefreshSettleGroup) : List UInt8 :=
  encodeUInt 1 message.mdUpdateAction
    ++ Alpha.encode message.mdEntryType
    ++ encodeUIntLE 8 message.productGuid
    ++ Alpha.encode message.clearingProductCode
    ++ Alpha.encode message.securityType
    ++ Alpha.encode message.securityExchange
    ++ MaturityMonthYear.encode message.maturityMonthYear
    ++ encodeUInt 1 message.putOrCall
    ++ StrikePrice.encode message.strikePrice
    ++ encodeUIntLE 8 message.underlyingProductGuid
    ++ Alpha.encode message.underlyingClearingProductCode
    ++ Alpha.encode message.underlyingSecurityType
    ++ Alpha.encode message.underlyingSecurityExchange
    ++ UnderlyingMaturityMonthYear.encode message.underlyingMaturityMonthYear
    ++ Alpha.encode message.symbol
    ++ encodeUIntLE 8 message.instrumentGuid
    ++ encodeUIntLE 4 message.securityId
    ++ FormattedLastPx.encode message.formattedLastPx
    ++ encodeUIntLE 8 message.mdEntryPx
    ++ encodeUIntLE 1 message.settlPriceType
    ++ encodeUIntLE 2 message.tradingReferenceDate
    ++ Alpha.encode message.mdStatisticDesc

def decode (bytes : List UInt8) : Option (IncrementalRefreshSettleGroup × List UInt8) := do
  let (mdUpdateAction, bytes) ← decodeUInt 1 bytes
  let (mdEntryType, bytes) ← Alpha.decode 1 bytes
  let (productGuid, bytes) ← decodeUIntLE 8 bytes
  let (clearingProductCode, bytes) ← Alpha.decode 12 bytes
  let (securityType, bytes) ← Alpha.decode 6 bytes
  let (securityExchange, bytes) ← Alpha.decode 8 bytes
  let (maturityMonthYear, bytes) ← MaturityMonthYear.decode bytes
  let (putOrCall, bytes) ← decodeUInt 1 bytes
  let (strikePrice, bytes) ← StrikePrice.decode bytes
  let (underlyingProductGuid, bytes) ← decodeUIntLE 8 bytes
  let (underlyingClearingProductCode, bytes) ← Alpha.decode 12 bytes
  let (underlyingSecurityType, bytes) ← Alpha.decode 6 bytes
  let (underlyingSecurityExchange, bytes) ← Alpha.decode 8 bytes
  let (underlyingMaturityMonthYear, bytes) ← UnderlyingMaturityMonthYear.decode bytes
  let (symbol, bytes) ← Alpha.decode 20 bytes
  let (instrumentGuid, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (formattedLastPx, bytes) ← FormattedLastPx.decode bytes
  let (mdEntryPx, bytes) ← decodeUIntLE 8 bytes
  let (settlPriceType, bytes) ← decodeUIntLE 1 bytes
  let (tradingReferenceDate, bytes) ← decodeUIntLE 2 bytes
  let (mdStatisticDesc, bytes) ← Alpha.decode 40 bytes
  pure ({ mdUpdateAction, mdEntryType, productGuid, clearingProductCode, securityType, securityExchange, maturityMonthYear, putOrCall, strikePrice, underlyingProductGuid, underlyingClearingProductCode, underlyingSecurityType, underlyingSecurityExchange, underlyingMaturityMonthYear, symbol, instrumentGuid, securityId, formattedLastPx, mdEntryPx, settlPriceType, tradingReferenceDate, mdStatisticDesc }, bytes)

@[simp] theorem encode_length (message : IncrementalRefreshSettleGroup) : (encode message).length = 182 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, encodeUIntLE_length, MaturityMonthYear.encode_length, StrikePrice.encode_length, UnderlyingMaturityMonthYear.encode_length, FormattedLastPx.encode_length]

theorem encode_length_pos (message : IncrementalRefreshSettleGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IncrementalRefreshSettleGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [MaturityMonthYear.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [StrikePrice.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [UnderlyingMaturityMonthYear.decode_encode, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [FormattedLastPx.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end IncrementalRefreshSettleGroup

/-- Incremental Refresh Settle Groups -/
structure IncrementalRefreshSettleGroups where
  blockLength : BitVec 16
  incrementalRefreshSettleGroup : Bounded 1 IncrementalRefreshSettleGroup
  deriving DecidableEq, Repr

namespace IncrementalRefreshSettleGroups

def encode (message : IncrementalRefreshSettleGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.incrementalRefreshSettleGroup.val.length)
    ++ encodeMany IncrementalRefreshSettleGroup.encode message.incrementalRefreshSettleGroup.val

def decode (bytes : List UInt8) : Option (IncrementalRefreshSettleGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (incrementalRefreshSettleGroup_, bytes) ← decodeMany IncrementalRefreshSettleGroup.decode numInGroup.toNat bytes
  if fits_incrementalRefreshSettleGroup : incrementalRefreshSettleGroup_.length < 256 ^ 1 then
    pure ({ blockLength, incrementalRefreshSettleGroup := ⟨incrementalRefreshSettleGroup_, fits_incrementalRefreshSettleGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : IncrementalRefreshSettleGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : IncrementalRefreshSettleGroups) : (encode message).length ≤ 46413 := by
  have bound_incrementalRefreshSettleGroup := message.incrementalRefreshSettleGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const IncrementalRefreshSettleGroup.encode 182 IncrementalRefreshSettleGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : IncrementalRefreshSettleGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeMany_bounded 1 IncrementalRefreshSettleGroup.encode IncrementalRefreshSettleGroup.decode IncrementalRefreshSettleGroup.decode_encode, Option.bind_some]
  dsimp only
  simp only [message.incrementalRefreshSettleGroup.length_lt, ↓reduceDIte]
  rfl

end IncrementalRefreshSettleGroups

/-- Md Incremental Refresh Settle -/
structure MdIncrementalRefreshSettle where
  transactTime : BitVec 64
  incrementalRefreshSettleGroups : IncrementalRefreshSettleGroups
  deriving DecidableEq, Repr

namespace MdIncrementalRefreshSettle

def encode (message : MdIncrementalRefreshSettle) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ IncrementalRefreshSettleGroups.encode message.incrementalRefreshSettleGroups

def decode (bytes : List UInt8) : Option (MdIncrementalRefreshSettle × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (incrementalRefreshSettleGroups, bytes) ← IncrementalRefreshSettleGroups.decode bytes
  pure ({ transactTime, incrementalRefreshSettleGroups }, bytes)

theorem encode_length_pos (message : MdIncrementalRefreshSettle) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MdIncrementalRefreshSettle) : (encode message).length ≤ 46421 := by
  have bound_incrementalRefreshSettleGroups := IncrementalRefreshSettleGroups.encode_length_le message.incrementalRefreshSettleGroups
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]
  omega

@[simp] theorem decode_encode (message : MdIncrementalRefreshSettle) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [IncrementalRefreshSettleGroups.decode_encode, Option.bind_some]
  rfl

end MdIncrementalRefreshSettle

/-- Incremental Refresh Voi Group: 131 bytes -/
structure IncrementalRefreshVoiGroup where
  productGuid : BitVec 64
  clearingProductCode : Alpha 12
  securityType : Alpha 6
  securityExchange : Alpha 8
  maturityMonthYear : MaturityMonthYear
  putOrCall : BitVec 8
  strikePrice : StrikePrice
  underlyingProductGuid : BitVec 64
  underlyingClearingProductCode : Alpha 12
  underlyingSecurityType : Alpha 6
  underlyingSecurityExchange : Alpha 8
  underlyingMaturityMonthYear : UnderlyingMaturityMonthYear
  symbol : Alpha 20
  instrumentGuid : BitVec 64
  securityId : BitVec 32
  clearedVolume : BitVec 32
  openInterestQty : BitVec 32
  openCloseSettlFlag : BitVec 8
  tradingReferenceDate : BitVec 16
  deriving DecidableEq, Repr

namespace IncrementalRefreshVoiGroup

def encode (message : IncrementalRefreshVoiGroup) : List UInt8 :=
  encodeUIntLE 8 message.productGuid
    ++ Alpha.encode message.clearingProductCode
    ++ Alpha.encode message.securityType
    ++ Alpha.encode message.securityExchange
    ++ MaturityMonthYear.encode message.maturityMonthYear
    ++ encodeUInt 1 message.putOrCall
    ++ StrikePrice.encode message.strikePrice
    ++ encodeUIntLE 8 message.underlyingProductGuid
    ++ Alpha.encode message.underlyingClearingProductCode
    ++ Alpha.encode message.underlyingSecurityType
    ++ Alpha.encode message.underlyingSecurityExchange
    ++ UnderlyingMaturityMonthYear.encode message.underlyingMaturityMonthYear
    ++ Alpha.encode message.symbol
    ++ encodeUIntLE 8 message.instrumentGuid
    ++ encodeUIntLE 4 message.securityId
    ++ encodeUIntLE 4 message.clearedVolume
    ++ encodeUIntLE 4 message.openInterestQty
    ++ encodeUInt 1 message.openCloseSettlFlag
    ++ encodeUIntLE 2 message.tradingReferenceDate

def decode (bytes : List UInt8) : Option (IncrementalRefreshVoiGroup × List UInt8) := do
  let (productGuid, bytes) ← decodeUIntLE 8 bytes
  let (clearingProductCode, bytes) ← Alpha.decode 12 bytes
  let (securityType, bytes) ← Alpha.decode 6 bytes
  let (securityExchange, bytes) ← Alpha.decode 8 bytes
  let (maturityMonthYear, bytes) ← MaturityMonthYear.decode bytes
  let (putOrCall, bytes) ← decodeUInt 1 bytes
  let (strikePrice, bytes) ← StrikePrice.decode bytes
  let (underlyingProductGuid, bytes) ← decodeUIntLE 8 bytes
  let (underlyingClearingProductCode, bytes) ← Alpha.decode 12 bytes
  let (underlyingSecurityType, bytes) ← Alpha.decode 6 bytes
  let (underlyingSecurityExchange, bytes) ← Alpha.decode 8 bytes
  let (underlyingMaturityMonthYear, bytes) ← UnderlyingMaturityMonthYear.decode bytes
  let (symbol, bytes) ← Alpha.decode 20 bytes
  let (instrumentGuid, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (clearedVolume, bytes) ← decodeUIntLE 4 bytes
  let (openInterestQty, bytes) ← decodeUIntLE 4 bytes
  let (openCloseSettlFlag, bytes) ← decodeUInt 1 bytes
  let (tradingReferenceDate, bytes) ← decodeUIntLE 2 bytes
  pure ({ productGuid, clearingProductCode, securityType, securityExchange, maturityMonthYear, putOrCall, strikePrice, underlyingProductGuid, underlyingClearingProductCode, underlyingSecurityType, underlyingSecurityExchange, underlyingMaturityMonthYear, symbol, instrumentGuid, securityId, clearedVolume, openInterestQty, openCloseSettlFlag, tradingReferenceDate }, bytes)

@[simp] theorem encode_length (message : IncrementalRefreshVoiGroup) : (encode message).length = 131 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, MaturityMonthYear.encode_length, encodeUInt_length, StrikePrice.encode_length, UnderlyingMaturityMonthYear.encode_length]

theorem encode_length_pos (message : IncrementalRefreshVoiGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IncrementalRefreshVoiGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [MaturityMonthYear.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [StrikePrice.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [UnderlyingMaturityMonthYear.decode_encode, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

end IncrementalRefreshVoiGroup

/-- Incremental Refresh Voi Groups -/
structure IncrementalRefreshVoiGroups where
  blockLength : BitVec 16
  incrementalRefreshVoiGroup : Bounded 1 IncrementalRefreshVoiGroup
  deriving DecidableEq, Repr

namespace IncrementalRefreshVoiGroups

def encode (message : IncrementalRefreshVoiGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.incrementalRefreshVoiGroup.val.length)
    ++ encodeMany IncrementalRefreshVoiGroup.encode message.incrementalRefreshVoiGroup.val

def decode (bytes : List UInt8) : Option (IncrementalRefreshVoiGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (incrementalRefreshVoiGroup_, bytes) ← decodeMany IncrementalRefreshVoiGroup.decode numInGroup.toNat bytes
  if fits_incrementalRefreshVoiGroup : incrementalRefreshVoiGroup_.length < 256 ^ 1 then
    pure ({ blockLength, incrementalRefreshVoiGroup := ⟨incrementalRefreshVoiGroup_, fits_incrementalRefreshVoiGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : IncrementalRefreshVoiGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : IncrementalRefreshVoiGroups) : (encode message).length ≤ 33408 := by
  have bound_incrementalRefreshVoiGroup := message.incrementalRefreshVoiGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const IncrementalRefreshVoiGroup.encode 131 IncrementalRefreshVoiGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : IncrementalRefreshVoiGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeMany_bounded 1 IncrementalRefreshVoiGroup.encode IncrementalRefreshVoiGroup.decode IncrementalRefreshVoiGroup.decode_encode, Option.bind_some]
  dsimp only
  simp only [message.incrementalRefreshVoiGroup.length_lt, ↓reduceDIte]
  rfl

end IncrementalRefreshVoiGroups

/-- Md Incremental Refresh Voi -/
structure MdIncrementalRefreshVoi where
  transactTime : BitVec 64
  incrementalRefreshVoiGroups : IncrementalRefreshVoiGroups
  deriving DecidableEq, Repr

namespace MdIncrementalRefreshVoi

def encode (message : MdIncrementalRefreshVoi) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ IncrementalRefreshVoiGroups.encode message.incrementalRefreshVoiGroups

def decode (bytes : List UInt8) : Option (MdIncrementalRefreshVoi × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (incrementalRefreshVoiGroups, bytes) ← IncrementalRefreshVoiGroups.decode bytes
  pure ({ transactTime, incrementalRefreshVoiGroups }, bytes)

theorem encode_length_pos (message : MdIncrementalRefreshVoi) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MdIncrementalRefreshVoi) : (encode message).length ≤ 33416 := by
  have bound_incrementalRefreshVoiGroups := IncrementalRefreshVoiGroups.encode_length_le message.incrementalRefreshVoiGroups
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]
  omega

@[simp] theorem decode_encode (message : MdIncrementalRefreshVoi) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [IncrementalRefreshVoiGroups.decode_encode, Option.bind_some]
  rfl

end MdIncrementalRefreshVoi

/-- Low Px: 9 bytes -/
structure LowPx where
  mantissa : BitVec 64
  exponent : BitVec 8
  deriving DecidableEq, Repr

namespace LowPx

def encode (message : LowPx) : List UInt8 :=
  encodeUIntLE 8 message.mantissa
    ++ encodeUInt 1 message.exponent

def decode (bytes : List UInt8) : Option (LowPx × List UInt8) := do
  let (mantissa, bytes) ← decodeUIntLE 8 bytes
  let (exponent, bytes) ← decodeUInt 1 bytes
  pure ({ mantissa, exponent }, bytes)

@[simp] theorem encode_length (message : LowPx) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : LowPx) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LowPx) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end LowPx

/-- High Px: 9 bytes -/
structure HighPx where
  mantissa : BitVec 64
  exponent : BitVec 8
  deriving DecidableEq, Repr

namespace HighPx

def encode (message : HighPx) : List UInt8 :=
  encodeUIntLE 8 message.mantissa
    ++ encodeUInt 1 message.exponent

def decode (bytes : List UInt8) : Option (HighPx × List UInt8) := do
  let (mantissa, bytes) ← decodeUIntLE 8 bytes
  let (exponent, bytes) ← decodeUInt 1 bytes
  pure ({ mantissa, exponent }, bytes)

@[simp] theorem encode_length (message : HighPx) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : HighPx) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : HighPx) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end HighPx

/-- Incremental Refresh High Low Group: 142 bytes -/
structure IncrementalRefreshHighLowGroup where
  productGuid : BitVec 64
  clearingProductCode : Alpha 12
  securityType : Alpha 6
  securityExchange : Alpha 8
  maturityMonthYear : MaturityMonthYear
  putOrCall : BitVec 8
  strikePrice : StrikePrice
  underlyingProductGuid : BitVec 64
  underlyingClearingProductCode : Alpha 12
  underlyingSecurityType : Alpha 6
  underlyingSecurityExchange : Alpha 8
  underlyingMaturityMonthYear : UnderlyingMaturityMonthYear
  symbol : Alpha 20
  instrumentGuid : BitVec 64
  securityId : BitVec 32
  lowPx : LowPx
  lowPxInd : LowPxInd
  highPx : HighPx
  highPxInd : HighPxInd
  tradingReferenceDate : BitVec 16
  deriving DecidableEq, Repr

namespace IncrementalRefreshHighLowGroup

def encode (message : IncrementalRefreshHighLowGroup) : List UInt8 :=
  encodeUIntLE 8 message.productGuid
    ++ Alpha.encode message.clearingProductCode
    ++ Alpha.encode message.securityType
    ++ Alpha.encode message.securityExchange
    ++ MaturityMonthYear.encode message.maturityMonthYear
    ++ encodeUInt 1 message.putOrCall
    ++ StrikePrice.encode message.strikePrice
    ++ encodeUIntLE 8 message.underlyingProductGuid
    ++ Alpha.encode message.underlyingClearingProductCode
    ++ Alpha.encode message.underlyingSecurityType
    ++ Alpha.encode message.underlyingSecurityExchange
    ++ UnderlyingMaturityMonthYear.encode message.underlyingMaturityMonthYear
    ++ Alpha.encode message.symbol
    ++ encodeUIntLE 8 message.instrumentGuid
    ++ encodeUIntLE 4 message.securityId
    ++ LowPx.encode message.lowPx
    ++ LowPxInd.encode message.lowPxInd
    ++ HighPx.encode message.highPx
    ++ HighPxInd.encode message.highPxInd
    ++ encodeUIntLE 2 message.tradingReferenceDate

def decode (bytes : List UInt8) : Option (IncrementalRefreshHighLowGroup × List UInt8) := do
  let (productGuid, bytes) ← decodeUIntLE 8 bytes
  let (clearingProductCode, bytes) ← Alpha.decode 12 bytes
  let (securityType, bytes) ← Alpha.decode 6 bytes
  let (securityExchange, bytes) ← Alpha.decode 8 bytes
  let (maturityMonthYear, bytes) ← MaturityMonthYear.decode bytes
  let (putOrCall, bytes) ← decodeUInt 1 bytes
  let (strikePrice, bytes) ← StrikePrice.decode bytes
  let (underlyingProductGuid, bytes) ← decodeUIntLE 8 bytes
  let (underlyingClearingProductCode, bytes) ← Alpha.decode 12 bytes
  let (underlyingSecurityType, bytes) ← Alpha.decode 6 bytes
  let (underlyingSecurityExchange, bytes) ← Alpha.decode 8 bytes
  let (underlyingMaturityMonthYear, bytes) ← UnderlyingMaturityMonthYear.decode bytes
  let (symbol, bytes) ← Alpha.decode 20 bytes
  let (instrumentGuid, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 4 bytes
  let (lowPx, bytes) ← LowPx.decode bytes
  let (lowPxInd, bytes) ← LowPxInd.decode bytes
  let (highPx, bytes) ← HighPx.decode bytes
  let (highPxInd, bytes) ← HighPxInd.decode bytes
  let (tradingReferenceDate, bytes) ← decodeUIntLE 2 bytes
  pure ({ productGuid, clearingProductCode, securityType, securityExchange, maturityMonthYear, putOrCall, strikePrice, underlyingProductGuid, underlyingClearingProductCode, underlyingSecurityType, underlyingSecurityExchange, underlyingMaturityMonthYear, symbol, instrumentGuid, securityId, lowPx, lowPxInd, highPx, highPxInd, tradingReferenceDate }, bytes)

@[simp] theorem encode_length (message : IncrementalRefreshHighLowGroup) : (encode message).length = 142 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, MaturityMonthYear.encode_length, encodeUInt_length, StrikePrice.encode_length, UnderlyingMaturityMonthYear.encode_length, LowPx.encode_length, LowPxInd.encode_length, HighPx.encode_length, HighPxInd.encode_length]

theorem encode_length_pos (message : IncrementalRefreshHighLowGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IncrementalRefreshHighLowGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [MaturityMonthYear.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [StrikePrice.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [UnderlyingMaturityMonthYear.decode_encode, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [LowPx.decode_encode, Option.bind_some]
  dsimp only
  rw [LowPxInd.decode_encode, Option.bind_some]
  dsimp only
  rw [HighPx.decode_encode, Option.bind_some]
  dsimp only
  rw [HighPxInd.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

end IncrementalRefreshHighLowGroup

/-- Incremental Refresh High Low Groups -/
structure IncrementalRefreshHighLowGroups where
  blockLength : BitVec 16
  incrementalRefreshHighLowGroup : Bounded 1 IncrementalRefreshHighLowGroup
  deriving DecidableEq, Repr

namespace IncrementalRefreshHighLowGroups

def encode (message : IncrementalRefreshHighLowGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.incrementalRefreshHighLowGroup.val.length)
    ++ encodeMany IncrementalRefreshHighLowGroup.encode message.incrementalRefreshHighLowGroup.val

def decode (bytes : List UInt8) : Option (IncrementalRefreshHighLowGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (incrementalRefreshHighLowGroup_, bytes) ← decodeMany IncrementalRefreshHighLowGroup.decode numInGroup.toNat bytes
  if fits_incrementalRefreshHighLowGroup : incrementalRefreshHighLowGroup_.length < 256 ^ 1 then
    pure ({ blockLength, incrementalRefreshHighLowGroup := ⟨incrementalRefreshHighLowGroup_, fits_incrementalRefreshHighLowGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : IncrementalRefreshHighLowGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : IncrementalRefreshHighLowGroups) : (encode message).length ≤ 36213 := by
  have bound_incrementalRefreshHighLowGroup := message.incrementalRefreshHighLowGroup.length_lt
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const IncrementalRefreshHighLowGroup.encode 142 IncrementalRefreshHighLowGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : IncrementalRefreshHighLowGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeMany_bounded 1 IncrementalRefreshHighLowGroup.encode IncrementalRefreshHighLowGroup.decode IncrementalRefreshHighLowGroup.decode_encode, Option.bind_some]
  dsimp only
  simp only [message.incrementalRefreshHighLowGroup.length_lt, ↓reduceDIte]
  rfl

end IncrementalRefreshHighLowGroups

/-- Md Incremental Refresh High Low -/
structure MdIncrementalRefreshHighLow where
  transactTime : BitVec 64
  incrementalRefreshHighLowGroups : IncrementalRefreshHighLowGroups
  deriving DecidableEq, Repr

namespace MdIncrementalRefreshHighLow

def encode (message : MdIncrementalRefreshHighLow) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ IncrementalRefreshHighLowGroups.encode message.incrementalRefreshHighLowGroups

def decode (bytes : List UInt8) : Option (MdIncrementalRefreshHighLow × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (incrementalRefreshHighLowGroups, bytes) ← IncrementalRefreshHighLowGroups.decode bytes
  pure ({ transactTime, incrementalRefreshHighLowGroups }, bytes)

theorem encode_length_pos (message : MdIncrementalRefreshHighLow) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MdIncrementalRefreshHighLow) : (encode message).length ≤ 36221 := by
  have bound_incrementalRefreshHighLowGroups := IncrementalRefreshHighLowGroups.encode_length_le message.incrementalRefreshHighLowGroups
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]
  omega

@[simp] theorem decode_encode (message : MdIncrementalRefreshHighLow) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [IncrementalRefreshHighLowGroups.decode_encode, Option.bind_some]
  rfl

end MdIncrementalRefreshHighLow

/-- Admin Heartbeat: 0 bytes -/
structure AdminHeartbeat where
  deriving DecidableEq, Repr

namespace AdminHeartbeat

def encode (_ : AdminHeartbeat) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (AdminHeartbeat × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : AdminHeartbeat) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : AdminHeartbeat) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end AdminHeartbeat

/-- Any Payload, selected by Template Id -/
inductive Payload where
  | mdIncrementalRefreshSettle (message : MdIncrementalRefreshSettle) -- 401
  | mdIncrementalRefreshVoi (message : MdIncrementalRefreshVoi) -- 402
  | mdIncrementalRefreshHighLow (message : MdIncrementalRefreshHighLow) -- 403
  | adminHeartbeat (message : AdminHeartbeat) -- 407
  deriving DecidableEq, Repr

namespace Payload

/-- The Template Id each message is sent under -/
def tag : Payload → BitVec 16
  | .mdIncrementalRefreshSettle _ => 401
  | .mdIncrementalRefreshVoi _ => 402
  | .mdIncrementalRefreshHighLow _ => 403
  | .adminHeartbeat _ => 407

def encode : Payload → List UInt8
  | .mdIncrementalRefreshSettle message => MdIncrementalRefreshSettle.encode message
  | .mdIncrementalRefreshVoi message => MdIncrementalRefreshVoi.encode message
  | .mdIncrementalRefreshHighLow message => MdIncrementalRefreshHighLow.encode message
  | .adminHeartbeat message => AdminHeartbeat.encode message

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 401 then (MdIncrementalRefreshSettle.decode bytes).map fun (message, rest) => (.mdIncrementalRefreshSettle message, rest)
  else if tag = 402 then (MdIncrementalRefreshVoi.decode bytes).map fun (message, rest) => (.mdIncrementalRefreshVoi message, rest)
  else if tag = 403 then (MdIncrementalRefreshHighLow.decode bytes).map fun (message, rest) => (.mdIncrementalRefreshHighLow message, rest)
  else if tag = 407 then (AdminHeartbeat.decode bytes).map fun (message, rest) => (.adminHeartbeat message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Message -/
structure Message where
  blockLength : BitVec 16
  schemaId : BitVec 16
  version : BitVec 16
  payload : Payload
  deriving DecidableEq, Repr

namespace Message

def encodeBody (message : Message) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUIntLE 2 (Payload.tag message.payload)
    ++ encodeUIntLE 2 message.schemaId
    ++ encodeUIntLE 2 message.version
    ++ Payload.encode message.payload

def decodeBody (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (templateId, bytes) ← decodeUIntLE 2 bytes
  let (schemaId, bytes) ← decodeUIntLE 2 bytes
  let (version, bytes) ← decodeUIntLE 2 bytes
  let (payload, bytes) ← Payload.decode templateId bytes
  pure ({ blockLength, schemaId, version, payload }, bytes)

theorem decodeBody_encodeBody (message : Message) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [Payload.decode_encode, Option.bind_some]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : Message) : (encodeBody message).length + 2 < 256 ^ 2 := by
  unfold encodeBody
  cases message.payload with
  | mdIncrementalRefreshSettle inner =>
    have bound_inner := MdIncrementalRefreshSettle.encode_length_le inner
    simp only [Payload.encode, List.length_append, encodeUIntLE_length]
    omega
  | mdIncrementalRefreshVoi inner =>
    have bound_inner := MdIncrementalRefreshVoi.encode_length_le inner
    simp only [Payload.encode, List.length_append, encodeUIntLE_length]
    omega
  | mdIncrementalRefreshHighLow inner =>
    have bound_inner := MdIncrementalRefreshHighLow.encode_length_le inner
    simp only [Payload.encode, List.length_append, encodeUIntLE_length]
    omega
  | adminHeartbeat inner =>
    simp only [Payload.encode, List.length_append, encodeUIntLE_length, AdminHeartbeat.encode_length]
    omega

/-- Size rule: Message Size counts the bytes after it plus 2, so it is written from the body and checked on decode -/
def encode : Message → List UInt8 :=
  encodeFramedLE 2 2 encodeBody

def decode : List UInt8 → Option (Message × List UInt8) :=
  decodeFramedLE 2 2 decodeBody

@[simp] theorem decode_encode (message : Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramedLE_encodeFramedLE 2 2 encodeBody decodeBody decodeBody_encodeBody encodeBody_length_lt message rest

theorem encode_length_pos (message : Message) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramedLE_length]
  omega

end Message

/-- Udp Packet -/
structure UdpPacket where
  binaryPacketHeader : BinaryPacketHeader
  message : List Message
  deriving DecidableEq, Repr

namespace UdpPacket

def encode (message : UdpPacket) : List UInt8 :=
  BinaryPacketHeader.encode message.binaryPacketHeader
    ++ encodeMany Message.encode message.message

def decode (bytes : List UInt8) : Option UdpPacket := do
  let (binaryPacketHeader, bytes) ← BinaryPacketHeader.decode bytes
  let message ← decodeAll Message.decode bytes.length bytes
  pure { binaryPacketHeader, message }

theorem encode_length_pos (message : UdpPacket) : (encode message).length > 0 := by
  unfold encode
  simp only [BinaryPacketHeader.encode_length, List.length_append]
  omega

theorem decode_encode (message : UdpPacket) : decode (encode message) = some message := by
  unfold decode encode
  simp only [Option.bind_eq_bind]
  rw [BinaryPacketHeader.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeAll_encodeMany Message.encode Message.decode Message.decode_encode Message.encode_length_pos message.message _ (encodeMany_length_ge Message.encode Message.encode_length_pos message.message), Option.bind_some]
  rfl

end UdpPacket

end Omi.CmeGlobexSettlementsSbeV70Udp
