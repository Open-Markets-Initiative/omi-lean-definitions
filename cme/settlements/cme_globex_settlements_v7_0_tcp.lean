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

namespace Omi.CmeGlobexSettlementsSbeV70Tcp

/-- Low Px Ind: one byte code -/
inductive LowPxInd where
  | ask -- Ask
  | bid -- Bid
  | trade -- Trade
  deriving DecidableEq, Repr

namespace LowPxInd

def toByte : LowPxInd → UInt8
  | .ask => 0x41
  | .bid => 0x42
  | .trade => 0x54

def ofByte? (byte : UInt8) : Option LowPxInd :=
  if byte = 0x41 then some .ask
  else if byte = 0x42 then some .bid
  else if byte = 0x54 then some .trade
  else none

theorem ofByte?_toByte (value : LowPxInd) : ofByte? value.toByte = some value := by
  cases value <;> decide

def encode (value : LowPxInd) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LowPxInd × List UInt8)
  | byte :: rest => (ofByte? byte).map fun value => (value, rest)
  | [] => none

@[simp] theorem encode_length (value : LowPxInd) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : LowPxInd) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte?_toByte]

end LowPxInd

/-- High Px Ind: one byte code -/
inductive HighPxInd where
  | ask -- Ask
  | bid -- Bid
  | trade -- Trade
  deriving DecidableEq, Repr

namespace HighPxInd

def toByte : HighPxInd → UInt8
  | .ask => 0x41
  | .bid => 0x42
  | .trade => 0x54

def ofByte? (byte : UInt8) : Option HighPxInd :=
  if byte = 0x41 then some .ask
  else if byte = 0x42 then some .bid
  else if byte = 0x54 then some .trade
  else none

theorem ofByte?_toByte (value : HighPxInd) : ofByte? value.toByte = some value := by
  cases value <;> decide

def encode (value : HighPxInd) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (HighPxInd × List UInt8)
  | byte :: rest => (ofByte? byte).map fun value => (value, rest)
  | [] => none

@[simp] theorem encode_length (value : HighPxInd) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : HighPxInd) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte?_toByte]

end HighPxInd

/-- Technical Header: 14 bytes -/
structure TechnicalHeader where
  encodingType : BitVec 16
  messageSequenceNumber : BitVec 32
  tcpSendingTime : BitVec 64
  deriving DecidableEq, Repr

namespace TechnicalHeader

def encode (message : TechnicalHeader) : List UInt8 :=
  encodeUIntLE 2 message.encodingType
    ++ encodeUIntLE 4 message.messageSequenceNumber
    ++ encodeUIntLE 8 message.tcpSendingTime

def decode (bytes : List UInt8) : Option (TechnicalHeader × List UInt8) := do
  let (encodingType, bytes) ← decodeUIntLE 2 bytes
  let (messageSequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (tcpSendingTime, bytes) ← decodeUIntLE 8 bytes
  pure ({ encodingType, messageSequenceNumber, tcpSendingTime }, bytes)

@[simp] theorem encode_length (message : TechnicalHeader) : (encode message).length = 14 := by
  simp [encode]

theorem encode_length_pos (message : TechnicalHeader) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : TechnicalHeader) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

end TechnicalHeader

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
  simp [encode]

theorem encode_length_pos (message : MaturityMonthYear) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : MaturityMonthYear) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

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
  simp [encode]

theorem encode_length_pos (message : StrikePrice) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : StrikePrice) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

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
  simp [encode]

theorem encode_length_pos (message : UnderlyingMaturityMonthYear) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : UnderlyingMaturityMonthYear) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

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
  simp [encode]

theorem encode_length_pos (message : FormattedLastPx) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : FormattedLastPx) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

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
  simp [encode]

theorem encode_length_pos (message : IncrementalRefreshSettleGroup) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : IncrementalRefreshSettleGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

end IncrementalRefreshSettleGroup

/-- Md Incremental Refresh Settle -/
structure MdIncrementalRefreshSettle where
  transactTime : BitVec 64
  blockLength : BitVec 16
  incrementalRefreshSettleGroup : Bounded 1 IncrementalRefreshSettleGroup
  deriving DecidableEq, Repr

namespace MdIncrementalRefreshSettle

def encode (message : MdIncrementalRefreshSettle) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat 8 message.incrementalRefreshSettleGroup.val.length)
    ++ encodeMany IncrementalRefreshSettleGroup.encode message.incrementalRefreshSettleGroup.val

def decode (bytes : List UInt8) : Option (MdIncrementalRefreshSettle × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (incrementalRefreshSettleGroup_, bytes) ← decodeMany IncrementalRefreshSettleGroup.decode numInGroup.toNat bytes
  if fits_incrementalRefreshSettleGroup : incrementalRefreshSettleGroup_.length < 256 then
    pure ({ transactTime, blockLength, incrementalRefreshSettleGroup := ⟨incrementalRefreshSettleGroup_, fits_incrementalRefreshSettleGroup⟩ }, bytes)
  else none

@[simp] theorem decode_encode (message : MdIncrementalRefreshSettle) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  have fits_incrementalRefreshSettleGroup : message.incrementalRefreshSettleGroup.val.length < 256 := by simpa using message.incrementalRefreshSettleGroup.length_lt
  simp [decode, encode, List.append_assoc, Nat.mod_eq_of_lt fits_incrementalRefreshSettleGroup, fits_incrementalRefreshSettleGroup, decodeMany_encodeMany IncrementalRefreshSettleGroup.encode IncrementalRefreshSettleGroup.decode IncrementalRefreshSettleGroup.decode_encode]

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
  simp [encode]

theorem encode_length_pos (message : IncrementalRefreshVoiGroup) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : IncrementalRefreshVoiGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

end IncrementalRefreshVoiGroup

/-- Md Incremental Refresh Voi -/
structure MdIncrementalRefreshVoi where
  transactTime : BitVec 64
  blockLength : BitVec 16
  incrementalRefreshVoiGroup : Bounded 1 IncrementalRefreshVoiGroup
  deriving DecidableEq, Repr

namespace MdIncrementalRefreshVoi

def encode (message : MdIncrementalRefreshVoi) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat 8 message.incrementalRefreshVoiGroup.val.length)
    ++ encodeMany IncrementalRefreshVoiGroup.encode message.incrementalRefreshVoiGroup.val

def decode (bytes : List UInt8) : Option (MdIncrementalRefreshVoi × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (incrementalRefreshVoiGroup_, bytes) ← decodeMany IncrementalRefreshVoiGroup.decode numInGroup.toNat bytes
  if fits_incrementalRefreshVoiGroup : incrementalRefreshVoiGroup_.length < 256 then
    pure ({ transactTime, blockLength, incrementalRefreshVoiGroup := ⟨incrementalRefreshVoiGroup_, fits_incrementalRefreshVoiGroup⟩ }, bytes)
  else none

@[simp] theorem decode_encode (message : MdIncrementalRefreshVoi) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  have fits_incrementalRefreshVoiGroup : message.incrementalRefreshVoiGroup.val.length < 256 := by simpa using message.incrementalRefreshVoiGroup.length_lt
  simp [decode, encode, List.append_assoc, Nat.mod_eq_of_lt fits_incrementalRefreshVoiGroup, fits_incrementalRefreshVoiGroup, decodeMany_encodeMany IncrementalRefreshVoiGroup.encode IncrementalRefreshVoiGroup.decode IncrementalRefreshVoiGroup.decode_encode]

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
  simp [encode]

theorem encode_length_pos (message : LowPx) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : LowPx) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

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
  simp [encode]

theorem encode_length_pos (message : HighPx) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : HighPx) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

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
  simp [encode]

theorem encode_length_pos (message : IncrementalRefreshHighLowGroup) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : IncrementalRefreshHighLowGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

end IncrementalRefreshHighLowGroup

/-- Md Incremental Refresh High Low -/
structure MdIncrementalRefreshHighLow where
  transactTime : BitVec 64
  blockLength : BitVec 16
  incrementalRefreshHighLowGroup : Bounded 1 IncrementalRefreshHighLowGroup
  deriving DecidableEq, Repr

namespace MdIncrementalRefreshHighLow

def encode (message : MdIncrementalRefreshHighLow) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat 8 message.incrementalRefreshHighLowGroup.val.length)
    ++ encodeMany IncrementalRefreshHighLowGroup.encode message.incrementalRefreshHighLowGroup.val

def decode (bytes : List UInt8) : Option (MdIncrementalRefreshHighLow × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (incrementalRefreshHighLowGroup_, bytes) ← decodeMany IncrementalRefreshHighLowGroup.decode numInGroup.toNat bytes
  if fits_incrementalRefreshHighLowGroup : incrementalRefreshHighLowGroup_.length < 256 then
    pure ({ transactTime, blockLength, incrementalRefreshHighLowGroup := ⟨incrementalRefreshHighLowGroup_, fits_incrementalRefreshHighLowGroup⟩ }, bytes)
  else none

@[simp] theorem decode_encode (message : MdIncrementalRefreshHighLow) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  have fits_incrementalRefreshHighLowGroup : message.incrementalRefreshHighLowGroup.val.length < 256 := by simpa using message.incrementalRefreshHighLowGroup.length_lt
  simp [decode, encode, List.append_assoc, Nat.mod_eq_of_lt fits_incrementalRefreshHighLowGroup, fits_incrementalRefreshHighLowGroup, decodeMany_encodeMany IncrementalRefreshHighLowGroup.encode IncrementalRefreshHighLowGroup.decode IncrementalRefreshHighLowGroup.decode_encode]

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
  simp [decode, encode, List.append_assoc]

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

/-- Tcp Message -/
structure TcpMessage where
  blockLength : BitVec 16
  schemaId : BitVec 16
  version : BitVec 16
  payload : Payload
  deriving DecidableEq, Repr

namespace TcpMessage

def encodeBody (message : TcpMessage) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ encodeUIntLE 2 (Payload.tag message.payload)
    ++ encodeUIntLE 2 message.schemaId
    ++ encodeUIntLE 2 message.version
    ++ Payload.encode message.payload

def decodeBody (bytes : List UInt8) : Option (TcpMessage × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (templateId, bytes) ← decodeUIntLE 2 bytes
  let (schemaId, bytes) ← decodeUIntLE 2 bytes
  let (version, bytes) ← decodeUIntLE 2 bytes
  let (payload, bytes) ← Payload.decode templateId bytes
  pure ({ blockLength, schemaId, version, payload }, bytes)

theorem decodeBody_encodeBody (message : TcpMessage) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  simp [decodeBody, encodeBody, List.append_assoc]

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : TcpMessage) : (encodeBody message).length + 2 < 65536 := by
  cases h : message.payload with
  | mdIncrementalRefreshSettle inner =>
    have bound_mdIncrementalRefreshSettle_incrementalRefreshSettleGroup := inner.incrementalRefreshSettleGroup.length_lt
    simp [encodeBody, h, Payload.encode, MdIncrementalRefreshSettle.encode, encodeMany_length_const IncrementalRefreshSettleGroup.encode 182 IncrementalRefreshSettleGroup.encode_length]
    omega
  | mdIncrementalRefreshVoi inner =>
    have bound_mdIncrementalRefreshVoi_incrementalRefreshVoiGroup := inner.incrementalRefreshVoiGroup.length_lt
    simp [encodeBody, h, Payload.encode, MdIncrementalRefreshVoi.encode, encodeMany_length_const IncrementalRefreshVoiGroup.encode 131 IncrementalRefreshVoiGroup.encode_length]
    omega
  | mdIncrementalRefreshHighLow inner =>
    have bound_mdIncrementalRefreshHighLow_incrementalRefreshHighLowGroup := inner.incrementalRefreshHighLowGroup.length_lt
    simp [encodeBody, h, Payload.encode, MdIncrementalRefreshHighLow.encode, encodeMany_length_const IncrementalRefreshHighLowGroup.encode 142 IncrementalRefreshHighLowGroup.encode_length]
    omega
  | adminHeartbeat inner =>
    simp [encodeBody, h, Payload.encode, AdminHeartbeat.encode]

/-- Size rule: Tcp Message Size counts the bytes after it plus 2, so it is written from the body -/
def encode : TcpMessage → List UInt8 :=
  encodeFramedLE 2 2 encodeBody

def decode : List UInt8 → Option (TcpMessage × List UInt8) :=
  decodeFramedLE 2 2 decodeBody

@[simp] theorem decode_encode (message : TcpMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramedLE_encodeFramedLE 2 2 encodeBody decodeBody decodeBody_encodeBody encodeBody_length_lt message rest

theorem encode_length_pos (message : TcpMessage) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramedLE_length]
  omega

end TcpMessage

/-- Tcp Packet -/
structure TcpPacket where
  technicalHeader : TechnicalHeader
  tcpMessage : List TcpMessage
  deriving DecidableEq, Repr

namespace TcpPacket

def encode (message : TcpPacket) : List UInt8 :=
  TechnicalHeader.encode message.technicalHeader
    ++ encodeMany TcpMessage.encode message.tcpMessage

def decode (bytes : List UInt8) : Option TcpPacket := do
  let (technicalHeader, bytes) ← TechnicalHeader.decode bytes
  let tcpMessage ← decodeAll TcpMessage.decode bytes.length bytes
  pure { technicalHeader, tcpMessage }

theorem decode_encode (message : TcpPacket) : decode (encode message) = some message := by
  simp [decode, encode, List.append_assoc, decodeAll_encodeMany TcpMessage.encode TcpMessage.decode TcpMessage.decode_encode TcpMessage.encode_length_pos message.tcpMessage _ (encodeMany_length_ge TcpMessage.encode TcpMessage.encode_length_pos message.tcpMessage)]

end TcpPacket

end Omi.CmeGlobexSettlementsSbeV70Tcp
