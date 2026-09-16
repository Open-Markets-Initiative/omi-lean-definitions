import Omi.Wire

/-!
# CME Group BrokerTec Us Treasuries v10.1

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.CmeGlobexBrokertecustSbeV101Tcp

/-- Md Entry Type: one byte code -/
inductive MdEntryType where
  | bid -- Bid
  | offer -- Offer
  | trade -- Trade
  | openPrice -- Open Price
  | closePrice -- Close Price
  | highTradePrice -- High Trade Price
  | lowTradePrice -- Low Trade Price
  | vwap -- Vwap
  | impliedBid -- Implied Bid
  | impliedOffer -- Implied Offer
  | bookReset -- Book Reset
  deriving DecidableEq, Repr

namespace MdEntryType

def toByte : MdEntryType → UInt8
  | .bid => 0x30
  | .offer => 0x31
  | .trade => 0x32
  | .openPrice => 0x34
  | .closePrice => 0x35
  | .highTradePrice => 0x37
  | .lowTradePrice => 0x38
  | .vwap => 0x39
  | .impliedBid => 0x45
  | .impliedOffer => 0x46
  | .bookReset => 0x4A

def ofByte? (byte : UInt8) : Option MdEntryType :=
  if byte = 0x30 then some .bid
  else if byte = 0x31 then some .offer
  else if byte = 0x32 then some .trade
  else if byte = 0x34 then some .openPrice
  else if byte = 0x35 then some .closePrice
  else if byte = 0x37 then some .highTradePrice
  else if byte = 0x38 then some .lowTradePrice
  else if byte = 0x39 then some .vwap
  else if byte = 0x45 then some .impliedBid
  else if byte = 0x46 then some .impliedOffer
  else if byte = 0x4A then some .bookReset
  else none

theorem ofByte?_toByte (value : MdEntryType) : ofByte? value.toByte = some value := by
  cases value <;> decide

def encode (value : MdEntryType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MdEntryType × List UInt8)
  | byte :: rest => (ofByte? byte).map fun value => (value, rest)
  | [] => none

@[simp] theorem encode_length (value : MdEntryType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : MdEntryType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte?_toByte]

end MdEntryType

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

/-- Md Entry Px: 9 bytes -/
structure MdEntryPx where
  mantissa : BitVec 64
  exponent : BitVec 8
  deriving DecidableEq, Repr

namespace MdEntryPx

def encode (message : MdEntryPx) : List UInt8 :=
  encodeUIntLE 8 message.mantissa
    ++ encodeUInt 1 message.exponent

def decode (bytes : List UInt8) : Option (MdEntryPx × List UInt8) := do
  let (mantissa, bytes) ← decodeUIntLE 8 bytes
  let (exponent, bytes) ← decodeUInt 1 bytes
  pure ({ mantissa, exponent }, bytes)

@[simp] theorem encode_length (message : MdEntryPx) : (encode message).length = 9 := by
  simp [encode]

theorem encode_length_pos (message : MdEntryPx) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : MdEntryPx) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

end MdEntryPx

/-- Coupon Rate: 5 bytes -/
structure CouponRate where
  mantissa32 : BitVec 32
  exponent : BitVec 8
  deriving DecidableEq, Repr

namespace CouponRate

def encode (message : CouponRate) : List UInt8 :=
  encodeUIntLE 4 message.mantissa32
    ++ encodeUInt 1 message.exponent

def decode (bytes : List UInt8) : Option (CouponRate × List UInt8) := do
  let (mantissa32, bytes) ← decodeUIntLE 4 bytes
  let (exponent, bytes) ← decodeUInt 1 bytes
  pure ({ mantissa32, exponent }, bytes)

@[simp] theorem encode_length (message : CouponRate) : (encode message).length = 5 := by
  simp [encode]

theorem encode_length_pos (message : CouponRate) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : CouponRate) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

end CouponRate

/-- Incremental Refresh Btec Group: 62 bytes -/
structure IncrementalRefreshBtecGroup where
  mdUpdateAction : BitVec 8
  mdEntryType : MdEntryType
  mdEntryPx : MdEntryPx
  mdEntrySize : BitVec 32
  mdPriceLevel : BitVec 8
  tradeVolume : BitVec 32
  symbol : Alpha 20
  maturityDate : BitVec 16
  securityAltId : Alpha 12
  securityAltIdSource : Alpha 1
  couponRate : CouponRate
  tradeCondition : Alpha 1
  priceType : BitVec 8
  deriving DecidableEq, Repr

namespace IncrementalRefreshBtecGroup

def encode (message : IncrementalRefreshBtecGroup) : List UInt8 :=
  encodeUInt 1 message.mdUpdateAction
    ++ MdEntryType.encode message.mdEntryType
    ++ MdEntryPx.encode message.mdEntryPx
    ++ encodeUIntLE 4 message.mdEntrySize
    ++ encodeUInt 1 message.mdPriceLevel
    ++ encodeUIntLE 4 message.tradeVolume
    ++ Alpha.encode message.symbol
    ++ encodeUIntLE 2 message.maturityDate
    ++ Alpha.encode message.securityAltId
    ++ Alpha.encode message.securityAltIdSource
    ++ CouponRate.encode message.couponRate
    ++ Alpha.encode message.tradeCondition
    ++ encodeUInt 1 message.priceType

def decode (bytes : List UInt8) : Option (IncrementalRefreshBtecGroup × List UInt8) := do
  let (mdUpdateAction, bytes) ← decodeUInt 1 bytes
  let (mdEntryType, bytes) ← MdEntryType.decode bytes
  let (mdEntryPx, bytes) ← MdEntryPx.decode bytes
  let (mdEntrySize, bytes) ← decodeUIntLE 4 bytes
  let (mdPriceLevel, bytes) ← decodeUInt 1 bytes
  let (tradeVolume, bytes) ← decodeUIntLE 4 bytes
  let (symbol, bytes) ← Alpha.decode 20 bytes
  let (maturityDate, bytes) ← decodeUIntLE 2 bytes
  let (securityAltId, bytes) ← Alpha.decode 12 bytes
  let (securityAltIdSource, bytes) ← Alpha.decode 1 bytes
  let (couponRate, bytes) ← CouponRate.decode bytes
  let (tradeCondition, bytes) ← Alpha.decode 1 bytes
  let (priceType, bytes) ← decodeUInt 1 bytes
  pure ({ mdUpdateAction, mdEntryType, mdEntryPx, mdEntrySize, mdPriceLevel, tradeVolume, symbol, maturityDate, securityAltId, securityAltIdSource, couponRate, tradeCondition, priceType }, bytes)

@[simp] theorem encode_length (message : IncrementalRefreshBtecGroup) : (encode message).length = 62 := by
  simp [encode]

theorem encode_length_pos (message : IncrementalRefreshBtecGroup) : (encode message).length > 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : IncrementalRefreshBtecGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode, List.append_assoc]

end IncrementalRefreshBtecGroup

/-- Md Incremental Refresh Btec -/
structure MdIncrementalRefreshBtec where
  tradeDate : BitVec 16
  transactTime : BitVec 64
  blockLength : BitVec 16
  incrementalRefreshBtecGroup : Bounded 1 IncrementalRefreshBtecGroup
  deriving DecidableEq, Repr

namespace MdIncrementalRefreshBtec

def encode (message : MdIncrementalRefreshBtec) : List UInt8 :=
  encodeUIntLE 2 message.tradeDate
    ++ encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 2 message.blockLength
    ++ encodeUInt 1 (BitVec.ofNat 8 message.incrementalRefreshBtecGroup.val.length)
    ++ encodeMany IncrementalRefreshBtecGroup.encode message.incrementalRefreshBtecGroup.val

def decode (bytes : List UInt8) : Option (MdIncrementalRefreshBtec × List UInt8) := do
  let (tradeDate, bytes) ← decodeUIntLE 2 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (incrementalRefreshBtecGroup_, bytes) ← decodeMany IncrementalRefreshBtecGroup.decode numInGroup.toNat bytes
  if fits_incrementalRefreshBtecGroup : incrementalRefreshBtecGroup_.length < 256 then
    pure ({ tradeDate, transactTime, blockLength, incrementalRefreshBtecGroup := ⟨incrementalRefreshBtecGroup_, fits_incrementalRefreshBtecGroup⟩ }, bytes)
  else none

@[simp] theorem decode_encode (message : MdIncrementalRefreshBtec) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  have fits_incrementalRefreshBtecGroup : message.incrementalRefreshBtecGroup.val.length < 256 := by simpa using message.incrementalRefreshBtecGroup.length_lt
  simp [decode, encode, List.append_assoc, Nat.mod_eq_of_lt fits_incrementalRefreshBtecGroup, fits_incrementalRefreshBtecGroup, decodeMany_encodeMany IncrementalRefreshBtecGroup.encode IncrementalRefreshBtecGroup.decode IncrementalRefreshBtecGroup.decode_encode]

end MdIncrementalRefreshBtec

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
  | mdIncrementalRefreshBtec (message : MdIncrementalRefreshBtec) -- 405
  | adminHeartbeat (message : AdminHeartbeat) -- 411
  deriving DecidableEq, Repr

namespace Payload

/-- The Template Id each message is sent under -/
def tag : Payload → BitVec 16
  | .mdIncrementalRefreshBtec _ => 405
  | .adminHeartbeat _ => 411

def encode : Payload → List UInt8
  | .mdIncrementalRefreshBtec message => MdIncrementalRefreshBtec.encode message
  | .adminHeartbeat message => AdminHeartbeat.encode message

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 405 then (MdIncrementalRefreshBtec.decode bytes).map fun (message, rest) => (.mdIncrementalRefreshBtec message, rest)
  else if tag = 411 then (AdminHeartbeat.decode bytes).map fun (message, rest) => (.adminHeartbeat message, rest)
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
  | mdIncrementalRefreshBtec inner =>
    have bound_mdIncrementalRefreshBtec_incrementalRefreshBtecGroup := inner.incrementalRefreshBtecGroup.length_lt
    simp [encodeBody, h, Payload.encode, MdIncrementalRefreshBtec.encode, encodeMany_length_const IncrementalRefreshBtecGroup.encode 62 IncrementalRefreshBtecGroup.encode_length]
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

end Omi.CmeGlobexBrokertecustSbeV101Tcp
