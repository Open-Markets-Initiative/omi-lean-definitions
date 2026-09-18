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
def MdEntryType.codes : List UInt8 :=
  [0x30, 0x31, 0x32, 0x34, 0x35, 0x37, 0x38, 0x39, 0x45, 0x46, 0x4A]

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
  | unlisted (byte : { byte : UInt8 // byte ∉ MdEntryType.codes }) -- any other code, kept as it is
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
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MdEntryType :=
  if byte = 0x30 then .bid
  else if byte = 0x31 then .offer
  else if byte = 0x32 then .trade
  else if byte = 0x34 then .openPrice
  else if byte = 0x35 then .closePrice
  else if byte = 0x37 then .highTradePrice
  else if byte = 0x38 then .lowTradePrice
  else if byte = 0x39 then .vwap
  else if byte = 0x45 then .impliedBid
  else if byte = 0x46 then .impliedOffer
  else .bookReset

def ofByte (byte : UInt8) : MdEntryType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MdEntryType) : ofByte value.toByte = value := by
  cases value with
  | bid => decide
  | offer => decide
  | trade => decide
  | openPrice => decide
  | closePrice => decide
  | highTradePrice => decide
  | lowTradePrice => decide
  | vwap => decide
  | impliedBid => decide
  | impliedOffer => decide
  | bookReset => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MdEntryType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MdEntryType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MdEntryType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : MdEntryType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

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
    ++ (encodeUIntLE 4 message.messageSequenceNumber
    ++ (encodeUIntLE 8 message.tcpSendingTime))

def decode (bytes : List UInt8) : Option (TechnicalHeader × List UInt8) := do
  let (encodingType, bytes) ← decodeUIntLE 2 bytes
  let (messageSequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (tcpSendingTime, bytes) ← decodeUIntLE 8 bytes
  pure ({ encodingType, messageSequenceNumber, tcpSendingTime }, bytes)

@[simp] theorem encode_length (message : TechnicalHeader) : (encode message).length = 14 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : TechnicalHeader) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TechnicalHeader) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TechnicalHeader

/-- Md Entry Px: 9 bytes -/
structure MdEntryPx where
  mantissa : BitVec 64
  exponent : BitVec 8
  deriving DecidableEq, Repr

namespace MdEntryPx

def encode (message : MdEntryPx) : List UInt8 :=
  encodeUIntLE 8 message.mantissa
    ++ (encodeUInt 1 message.exponent)

def decode (bytes : List UInt8) : Option (MdEntryPx × List UInt8) := do
  let (mantissa, bytes) ← decodeUIntLE 8 bytes
  let (exponent, bytes) ← decodeUInt 1 bytes
  pure ({ mantissa, exponent }, bytes)

@[simp] theorem encode_length (message : MdEntryPx) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : MdEntryPx) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MdEntryPx) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end MdEntryPx

/-- Coupon Rate: 5 bytes -/
structure CouponRate where
  mantissa32 : BitVec 32
  exponent : BitVec 8
  deriving DecidableEq, Repr

namespace CouponRate

def encode (message : CouponRate) : List UInt8 :=
  encodeUIntLE 4 message.mantissa32
    ++ (encodeUInt 1 message.exponent)

def decode (bytes : List UInt8) : Option (CouponRate × List UInt8) := do
  let (mantissa32, bytes) ← decodeUIntLE 4 bytes
  let (exponent, bytes) ← decodeUInt 1 bytes
  pure ({ mantissa32, exponent }, bytes)

@[simp] theorem encode_length (message : CouponRate) : (encode message).length = 5 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : CouponRate) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CouponRate) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

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
    ++ (MdEntryType.encode message.mdEntryType
    ++ (MdEntryPx.encode message.mdEntryPx
    ++ (encodeUIntLE 4 message.mdEntrySize
    ++ (encodeUInt 1 message.mdPriceLevel
    ++ (encodeUIntLE 4 message.tradeVolume
    ++ (Alpha.encode message.symbol
    ++ (encodeUIntLE 2 message.maturityDate
    ++ (Alpha.encode message.securityAltId
    ++ (Alpha.encode message.securityAltIdSource
    ++ (CouponRate.encode message.couponRate
    ++ (Alpha.encode message.tradeCondition
    ++ (encodeUInt 1 message.priceType))))))))))))

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
  unfold encode
  simp only [List.length_append, encodeUInt_length, MdEntryType.encode_length, MdEntryPx.encode_length, encodeUIntLE_length, Alpha.encode_length, CouponRate.encode_length]

theorem encode_length_pos (message : IncrementalRefreshBtecGroup) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IncrementalRefreshBtecGroup) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, MdEntryType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, MdEntryPx.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CouponRate.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end IncrementalRefreshBtecGroup

/-- Incremental Refresh Btec Groups -/
structure IncrementalRefreshBtecGroups where
  blockLength : BitVec 16
  incrementalRefreshBtecGroup : Bounded 1 IncrementalRefreshBtecGroup
  deriving DecidableEq, Repr

namespace IncrementalRefreshBtecGroups

def encode (message : IncrementalRefreshBtecGroups) : List UInt8 :=
  encodeUIntLE 2 message.blockLength
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.incrementalRefreshBtecGroup.val.length)
    ++ (encodeMany IncrementalRefreshBtecGroup.encode message.incrementalRefreshBtecGroup.val))

def decode (bytes : List UInt8) : Option (IncrementalRefreshBtecGroups × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (numInGroup, bytes) ← decodeUInt 1 bytes
  let (incrementalRefreshBtecGroup_, bytes) ← decodeMany IncrementalRefreshBtecGroup.decode numInGroup.toNat bytes
  if fits_incrementalRefreshBtecGroup : incrementalRefreshBtecGroup_.length < 256 ^ 1 then
    pure ({ blockLength, incrementalRefreshBtecGroup := ⟨incrementalRefreshBtecGroup_, fits_incrementalRefreshBtecGroup⟩ }, bytes)
  else none

theorem encode_length_pos (message : IncrementalRefreshBtecGroups) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : IncrementalRefreshBtecGroups) : (encode message).length ≤ 15813 := by
  have bound_incrementalRefreshBtecGroup := message.incrementalRefreshBtecGroup.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const IncrementalRefreshBtecGroup.encode 62 IncrementalRefreshBtecGroup.encode_length]
  omega

@[simp] theorem decode_encode (message : IncrementalRefreshBtecGroups) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 IncrementalRefreshBtecGroup.encode IncrementalRefreshBtecGroup.decode IncrementalRefreshBtecGroup.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.incrementalRefreshBtecGroup.length_lt]
  rfl

end IncrementalRefreshBtecGroups

/-- Md Incremental Refresh Btec -/
structure MdIncrementalRefreshBtec where
  tradeDate : BitVec 16
  transactTime : BitVec 64
  incrementalRefreshBtecGroups : IncrementalRefreshBtecGroups
  deriving DecidableEq, Repr

namespace MdIncrementalRefreshBtec

def encode (message : MdIncrementalRefreshBtec) : List UInt8 :=
  encodeUIntLE 2 message.tradeDate
    ++ (encodeUIntLE 8 message.transactTime
    ++ (IncrementalRefreshBtecGroups.encode message.incrementalRefreshBtecGroups))

def decode (bytes : List UInt8) : Option (MdIncrementalRefreshBtec × List UInt8) := do
  let (tradeDate, bytes) ← decodeUIntLE 2 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (incrementalRefreshBtecGroups, bytes) ← IncrementalRefreshBtecGroups.decode bytes
  pure ({ tradeDate, transactTime, incrementalRefreshBtecGroups }, bytes)

theorem encode_length_pos (message : MdIncrementalRefreshBtec) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MdIncrementalRefreshBtec) : (encode message).length ≤ 15823 := by
  have bound_incrementalRefreshBtecGroups := IncrementalRefreshBtecGroups.encode_length_le message.incrementalRefreshBtecGroups
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
  omega

@[simp] theorem decode_encode (message : MdIncrementalRefreshBtec) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [IncrementalRefreshBtecGroups.decode_encode, some_bind]
  rfl

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
  simp [decode, encode]

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
    ++ (encodeUIntLE 2 (Payload.tag message.payload)
    ++ (encodeUIntLE 2 message.schemaId
    ++ (encodeUIntLE 2 message.version
    ++ (Payload.encode message.payload))))

def decodeBody (bytes : List UInt8) : Option (TcpMessage × List UInt8) := do
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (templateId, bytes) ← decodeUIntLE 2 bytes
  let (schemaId, bytes) ← decodeUIntLE 2 bytes
  let (version, bytes) ← decodeUIntLE 2 bytes
  let (payload, bytes) ← Payload.decode templateId bytes
  pure ({ blockLength, schemaId, version, payload }, bytes)

theorem decodeBody_encodeBody (message : TcpMessage) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Payload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : TcpMessage) : (encodeBody message).length + 2 < 256 ^ 2 := by
  unfold encodeBody
  cases message.payload with
  | mdIncrementalRefreshBtec inner =>
    have bound_inner := MdIncrementalRefreshBtec.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | adminHeartbeat inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, AdminHeartbeat.encode_length]
    omega

/-- Size rule: Tcp Message Size counts the bytes after it plus 2, so it is written from the body and checked on decode -/
def encode : TcpMessage → List UInt8 :=
  encodeFramedLE 2 2 encodeBody

def decode : List UInt8 → Option (TcpMessage × List UInt8) :=
  decodeFramedLE 2 2 decodeBody

@[simp] theorem decode_encode (message : TcpMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramedLE_encodeFramedLE 2 2 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

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
    ++ (encodeMany TcpMessage.encode message.tcpMessage)

def decode (bytes : List UInt8) : Option TcpPacket := do
  let (technicalHeader, bytes) ← TechnicalHeader.decode bytes
  let tcpMessage ← decodeAll TcpMessage.decode bytes.length bytes
  pure { technicalHeader, tcpMessage }

theorem encode_length_pos (message : TcpPacket) : (encode message).length > 0 := by
  unfold encode
  simp only [TechnicalHeader.encode_length, List.length_append]
  omega

theorem decode_encode (message : TcpPacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [TechnicalHeader.decode_encode, some_bind]
  dsimp only
  rw [decodeAll_encodeMany TcpMessage.encode TcpMessage.decode TcpMessage.decode_encode TcpMessage.encode_length_pos message.tcpMessage _ (encodeMany_length_ge TcpMessage.encode TcpMessage.encode_length_pos message.tcpMessage), some_bind]
  rfl

end TcpPacket

end Omi.CmeGlobexBrokertecustSbeV101Tcp
