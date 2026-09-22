import Omi.Wire

/-!
# National Association of Securities Dealers Automated Quotations (Nasdaq) Phlx Options Spread Trade Feed v2.1

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: a Message Count of 0 marks Heartbeat and carries no messages; the decoder reads it as a count and the encoder never writes it.

Note: a Message Count of 65535 marks End Of Session and carries no messages; the decoder reads it as a count and the encoder never writes it.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NasdaqMrxoptionsSpreadtradefeedItchV21MoldUdp64

/-- System Event Message: 11 bytes -/
structure SystemEventMessage where
  trackingNumber : BitVec 16
  timestamp : BitVec 64
  eventCode : Alpha 1
  deriving DecidableEq, Repr

namespace SystemEventMessage

def encode (message : SystemEventMessage) : List UInt8 :=
  encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 8 message.timestamp
    ++ (Alpha.encode message.eventCode))

def decode (bytes : List UInt8) : Option (SystemEventMessage × List UInt8) := do
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (eventCode, bytes) ← Alpha.decode 1 bytes
  pure ({ trackingNumber, timestamp, eventCode }, bytes)

@[simp] theorem encode_length (message : SystemEventMessage) : (encode message).length = 11 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : SystemEventMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SystemEventMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SystemEventMessage

/-- Leg Information: 25 bytes -/
structure LegInformation where
  optionId : BitVec 32
  securitySymbol : Alpha 8
  expirationYear : BitVec 8
  expirationMonth : BitVec 8
  expirationDay : BitVec 8
  explicitStrikePrice : BitVec 32
  optionType : Alpha 1
  side : Alpha 1
  legRatio : BitVec 32
  deriving DecidableEq, Repr

namespace LegInformation

def encode (message : LegInformation) : List UInt8 :=
  encodeUInt 4 message.optionId
    ++ (Alpha.encode message.securitySymbol
    ++ (encodeUInt 1 message.expirationYear
    ++ (encodeUInt 1 message.expirationMonth
    ++ (encodeUInt 1 message.expirationDay
    ++ (encodeUInt 4 message.explicitStrikePrice
    ++ (Alpha.encode message.optionType
    ++ (Alpha.encode message.side
    ++ (encodeUInt 4 message.legRatio))))))))

def decode (bytes : List UInt8) : Option (LegInformation × List UInt8) := do
  let (optionId, bytes) ← decodeUInt 4 bytes
  let (securitySymbol, bytes) ← Alpha.decode 8 bytes
  let (expirationYear, bytes) ← decodeUInt 1 bytes
  let (expirationMonth, bytes) ← decodeUInt 1 bytes
  let (expirationDay, bytes) ← decodeUInt 1 bytes
  let (explicitStrikePrice, bytes) ← decodeUInt 4 bytes
  let (optionType, bytes) ← Alpha.decode 1 bytes
  let (side, bytes) ← Alpha.decode 1 bytes
  let (legRatio, bytes) ← decodeUInt 4 bytes
  pure ({ optionId, securitySymbol, expirationYear, expirationMonth, expirationDay, explicitStrikePrice, optionType, side, legRatio }, bytes)

@[simp] theorem encode_length (message : LegInformation) : (encode message).length = 25 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : LegInformation) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LegInformation) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end LegInformation

/-- Complex Strategy Directory Message -/
structure ComplexStrategyDirectoryMessage where
  trackingNumber : BitVec 16
  timestamp : BitVec 64
  strategyId : BitVec 32
  strategyType : Alpha 1
  underlyingSymbol : Alpha 13
  reserved16 : Alpha 16
  legInformation : Bounded 1 LegInformation
  deriving DecidableEq, Repr

namespace ComplexStrategyDirectoryMessage

def encode (message : ComplexStrategyDirectoryMessage) : List UInt8 :=
  encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.strategyId
    ++ (Alpha.encode message.strategyType
    ++ (Alpha.encode message.underlyingSymbol
    ++ (Alpha.encode message.reserved16
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.legInformation.val.length)
    ++ (encodeMany LegInformation.encode message.legInformation.val)))))))

def decode (bytes : List UInt8) : Option (ComplexStrategyDirectoryMessage × List UInt8) := do
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (strategyId, bytes) ← decodeUInt 4 bytes
  let (strategyType, bytes) ← Alpha.decode 1 bytes
  let (underlyingSymbol, bytes) ← Alpha.decode 13 bytes
  let (reserved16, bytes) ← Alpha.decode 16 bytes
  let (numberOfLegs, bytes) ← decodeUInt 1 bytes
  let (legInformation_, bytes) ← decodeMany LegInformation.decode numberOfLegs.toNat bytes
  if fits_legInformation : legInformation_.length < 256 ^ 1 then
    pure ({ trackingNumber, timestamp, strategyId, strategyType, underlyingSymbol, reserved16, legInformation := ⟨legInformation_, fits_legInformation⟩ }, bytes)
  else none

theorem encode_length_pos (message : ComplexStrategyDirectoryMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ComplexStrategyDirectoryMessage) : (encode message).length ≤ 6420 := by
  have bound_legInformation := message.legInformation.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUInt_length, Alpha.encode_length, encodeMany_length_const LegInformation.encode 25 LegInformation.encode_length]
  omega

@[simp] theorem decode_encode (message : ComplexStrategyDirectoryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 LegInformation.encode LegInformation.decode LegInformation.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.legInformation.length_lt]
  rfl

end ComplexStrategyDirectoryMessage

/-- Strategy Trading Action Message: 15 bytes -/
structure StrategyTradingActionMessage where
  trackingNumber : BitVec 16
  timestamp : BitVec 64
  strategyId : BitVec 32
  currentTradingState : Alpha 1
  deriving DecidableEq, Repr

namespace StrategyTradingActionMessage

def encode (message : StrategyTradingActionMessage) : List UInt8 :=
  encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.strategyId
    ++ (Alpha.encode message.currentTradingState)))

def decode (bytes : List UInt8) : Option (StrategyTradingActionMessage × List UInt8) := do
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (strategyId, bytes) ← decodeUInt 4 bytes
  let (currentTradingState, bytes) ← Alpha.decode 1 bytes
  pure ({ trackingNumber, timestamp, strategyId, currentTradingState }, bytes)

@[simp] theorem encode_length (message : StrategyTradingActionMessage) : (encode message).length = 15 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : StrategyTradingActionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StrategyTradingActionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end StrategyTradingActionMessage

/-- Complex Strategy Trade Report: 43 bytes -/
structure ComplexStrategyTradeReport where
  trackingNumber : BitVec 16
  timestamp : BitVec 64
  strategyId : BitVec 32
  crossId : BitVec 32
  tradeCondition : BitVec 8
  price : BitVec 32
  volume : BitVec 32
  reserved16 : Alpha 16
  deriving DecidableEq, Repr

namespace ComplexStrategyTradeReport

def encode (message : ComplexStrategyTradeReport) : List UInt8 :=
  encodeUInt 2 message.trackingNumber
    ++ (encodeUInt 8 message.timestamp
    ++ (encodeUInt 4 message.strategyId
    ++ (encodeUInt 4 message.crossId
    ++ (encodeUInt 1 message.tradeCondition
    ++ (encodeUInt 4 message.price
    ++ (encodeUInt 4 message.volume
    ++ (Alpha.encode message.reserved16)))))))

def decode (bytes : List UInt8) : Option (ComplexStrategyTradeReport × List UInt8) := do
  let (trackingNumber, bytes) ← decodeUInt 2 bytes
  let (timestamp, bytes) ← decodeUInt 8 bytes
  let (strategyId, bytes) ← decodeUInt 4 bytes
  let (crossId, bytes) ← decodeUInt 4 bytes
  let (tradeCondition, bytes) ← decodeUInt 1 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (volume, bytes) ← decodeUInt 4 bytes
  let (reserved16, bytes) ← Alpha.decode 16 bytes
  pure ({ trackingNumber, timestamp, strategyId, crossId, tradeCondition, price, volume, reserved16 }, bytes)

@[simp] theorem encode_length (message : ComplexStrategyTradeReport) : (encode message).length = 43 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : ComplexStrategyTradeReport) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ComplexStrategyTradeReport) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ComplexStrategyTradeReport

/-- Any Udp Payload, selected by Message Type -/
inductive UdpPayload where
  | systemEventMessage (message : SystemEventMessage) -- "S" 0x53
  | complexStrategyDirectoryMessage (message : ComplexStrategyDirectoryMessage) -- "s" 0x73
  | strategyTradingActionMessage (message : StrategyTradingActionMessage) -- "H" 0x48
  | complexStrategyTradeReport (message : ComplexStrategyTradeReport) -- "R" 0x52
  deriving DecidableEq, Repr

namespace UdpPayload

/-- The Message Type each message is sent under -/
def tag : UdpPayload → BitVec 8
  | .systemEventMessage _ => 83
  | .complexStrategyDirectoryMessage _ => 115
  | .strategyTradingActionMessage _ => 72
  | .complexStrategyTradeReport _ => 82

def encode : UdpPayload → List UInt8
  | .systemEventMessage message => SystemEventMessage.encode message
  | .complexStrategyDirectoryMessage message => ComplexStrategyDirectoryMessage.encode message
  | .strategyTradingActionMessage message => StrategyTradingActionMessage.encode message
  | .complexStrategyTradeReport message => ComplexStrategyTradeReport.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : UdpPayload) : (encode message).length ≤ 6420 := by
  cases message with
  | systemEventMessage inner =>
    simp only [encode, SystemEventMessage.encode_length]
    omega
  | complexStrategyDirectoryMessage inner =>
    have bound_inner := ComplexStrategyDirectoryMessage.encode_length_le inner
    simp only [encode]
    omega
  | strategyTradingActionMessage inner =>
    simp only [encode, StrategyTradingActionMessage.encode_length]
    omega
  | complexStrategyTradeReport inner =>
    simp only [encode, ComplexStrategyTradeReport.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (UdpPayload × List UInt8) :=
  if tag = 83 then (SystemEventMessage.decode bytes).map fun (message, rest) => (.systemEventMessage message, rest)
  else if tag = 115 then (ComplexStrategyDirectoryMessage.decode bytes).map fun (message, rest) => (.complexStrategyDirectoryMessage message, rest)
  else if tag = 72 then (StrategyTradingActionMessage.decode bytes).map fun (message, rest) => (.strategyTradingActionMessage message, rest)
  else if tag = 82 then (ComplexStrategyTradeReport.decode bytes).map fun (message, rest) => (.complexStrategyTradeReport message, rest)
  else none

@[simp] theorem decode_encode (message : UdpPayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end UdpPayload

/-- Message -/
structure Message where
  udpPayload : UdpPayload
  deriving DecidableEq, Repr

namespace Message

def encodeBody (message : Message) : List UInt8 :=
  encodeUInt 1 (UdpPayload.tag message.udpPayload)
    ++ (UdpPayload.encode message.udpPayload)

def decodeBody (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (messageType, bytes) ← decodeUInt 1 bytes
  let (udpPayload, bytes) ← UdpPayload.decode messageType bytes
  pure ({ udpPayload }, bytes)

theorem decodeBody_encodeBody (message : Message) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [UdpPayload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : Message) : (encodeBody message).length + 0 < 256 ^ 2 := by
  unfold encodeBody
  cases message.udpPayload with
  | systemEventMessage inner =>
    simp only [UdpPayload.encode, List.length_append, encodeUInt_length, SystemEventMessage.encode_length]
    omega
  | complexStrategyDirectoryMessage inner =>
    have bound_inner := ComplexStrategyDirectoryMessage.encode_length_le inner
    simp only [UdpPayload.encode, List.length_append, encodeUInt_length]
    omega
  | strategyTradingActionMessage inner =>
    simp only [UdpPayload.encode, List.length_append, encodeUInt_length, StrategyTradingActionMessage.encode_length]
    omega
  | complexStrategyTradeReport inner =>
    simp only [UdpPayload.encode, List.length_append, encodeUInt_length, ComplexStrategyTradeReport.encode_length]
    omega

/-- Size rule: Message Length counts the bytes after it, so it is written from the body and checked on decode -/
def encode : Message → List UInt8 :=
  encodeFramed 2 0 encodeBody

def decode : List UInt8 → Option (Message × List UInt8) :=
  decodeFramed 2 0 decodeBody

@[simp] theorem decode_encode (message : Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramed_encodeFramed 2 0 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : Message) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramed_length]
  omega

end Message

/-- Mold Udp 64 Packet -/
structure MoldUdp64Packet where
  udpSession : Alpha 10
  udpSequenceNumber : BitVec 64
  message : Bounded 2 Message
  deriving DecidableEq, Repr

namespace MoldUdp64Packet

def encode (message : MoldUdp64Packet) : List UInt8 :=
  Alpha.encode message.udpSession
    ++ (encodeUInt 8 message.udpSequenceNumber
    ++ (encodeUInt 2 (BitVec.ofNat (8 * 2) message.message.val.length)
    ++ (encodeMany Message.encode message.message.val)))

def decode (bytes : List UInt8) : Option (MoldUdp64Packet × List UInt8) := do
  let (udpSession, bytes) ← Alpha.decode 10 bytes
  let (udpSequenceNumber, bytes) ← decodeUInt 8 bytes
  let (messageCount, bytes) ← decodeUInt 2 bytes
  let (message_, bytes) ← decodeMany Message.decode messageCount.toNat bytes
  if fits_message : message_.length < 256 ^ 2 then
    pure ({ udpSession, udpSequenceNumber, message := ⟨message_, fits_message⟩ }, bytes)
  else none

theorem encode_length_pos (message : MoldUdp64Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

@[simp] theorem decode_encode (message : MoldUdp64Packet) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 Message.encode Message.decode Message.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.message.length_lt]
  rfl

end MoldUdp64Packet

end Omi.NasdaqMrxoptionsSpreadtradefeedItchV21MoldUdp64
