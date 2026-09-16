import Omi.Wire

/-!
# Japan Exchange Group Genium Inet v5.0

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Sequenced Data Packet is not framed: its length Packet Length is not the integer that leads it.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.JpxOsederivativesGeniuminetOuchV50Server

/-- Side: one byte code -/
def Side.codes : List UInt8 :=
  [0x42, 0x53]

inductive Side where
  | buy -- Buy
  | sell -- Sell
  | unlisted (byte : { byte : UInt8 // byte ∉ Side.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Side

def toByte : Side → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Side :=
  if byte = 0x42 then .buy
  else .sell

def ofByte (byte : UInt8) : Side :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Side) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Side) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Side × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Side) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Side) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Side

/-- Debug Packet: 1 bytes -/
structure DebugPacket where
  text : Alpha 1
  deriving DecidableEq, Repr

namespace DebugPacket

def encode (message : DebugPacket) : List UInt8 :=
  Alpha.encode message.text

def decode (bytes : List UInt8) : Option (DebugPacket × List UInt8) := do
  let (text, bytes) ← Alpha.decode 1 bytes
  pure ({ text }, bytes)

@[simp] theorem encode_length (message : DebugPacket) : (encode message).length = 1 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : DebugPacket) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DebugPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [Option.bind_eq_bind]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end DebugPacket

/-- Login Accepted Packet: 30 bytes -/
structure LoginAcceptedPacket where
  session : Alpha 10
  sequenceNumber : Alpha 20
  deriving DecidableEq, Repr

namespace LoginAcceptedPacket

def encode (message : LoginAcceptedPacket) : List UInt8 :=
  Alpha.encode message.session
    ++ Alpha.encode message.sequenceNumber

def decode (bytes : List UInt8) : Option (LoginAcceptedPacket × List UInt8) := do
  let (session, bytes) ← Alpha.decode 10 bytes
  let (sequenceNumber, bytes) ← Alpha.decode 20 bytes
  pure ({ session, sequenceNumber }, bytes)

@[simp] theorem encode_length (message : LoginAcceptedPacket) : (encode message).length = 30 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : LoginAcceptedPacket) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginAcceptedPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end LoginAcceptedPacket

/-- Login Rejected Packet: 1 bytes -/
structure LoginRejectedPacket where
  rejectReasonCode : Alpha 1
  deriving DecidableEq, Repr

namespace LoginRejectedPacket

def encode (message : LoginRejectedPacket) : List UInt8 :=
  Alpha.encode message.rejectReasonCode

def decode (bytes : List UInt8) : Option (LoginRejectedPacket × List UInt8) := do
  let (rejectReasonCode, bytes) ← Alpha.decode 1 bytes
  pure ({ rejectReasonCode }, bytes)

@[simp] theorem encode_length (message : LoginRejectedPacket) : (encode message).length = 1 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : LoginRejectedPacket) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoginRejectedPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [Option.bind_eq_bind]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end LoginRejectedPacket

/-- Order Accepted: 113 bytes -/
structure OrderAccepted where
  timestampNanoseconds : BitVec 64
  orderToken : Alpha 14
  orderBookId : BitVec 32
  side : Side
  orderId : BitVec 64
  quantity : BitVec 64
  price : BitVec 32
  timeInForce : BitVec 8
  openClose : BitVec 8
  clientAccount : Alpha 16
  orderState : BitVec 8
  customerInfo : Alpha 15
  exchangeInfo : Alpha 32
  deriving DecidableEq, Repr

namespace OrderAccepted

def encode (message : OrderAccepted) : List UInt8 :=
  encodeUInt 8 message.timestampNanoseconds
    ++ Alpha.encode message.orderToken
    ++ encodeUInt 4 message.orderBookId
    ++ Side.encode message.side
    ++ encodeUInt 8 message.orderId
    ++ encodeUInt 8 message.quantity
    ++ encodeUInt 4 message.price
    ++ encodeUInt 1 message.timeInForce
    ++ encodeUInt 1 message.openClose
    ++ Alpha.encode message.clientAccount
    ++ encodeUInt 1 message.orderState
    ++ Alpha.encode message.customerInfo
    ++ Alpha.encode message.exchangeInfo

def decode (bytes : List UInt8) : Option (OrderAccepted × List UInt8) := do
  let (timestampNanoseconds, bytes) ← decodeUInt 8 bytes
  let (orderToken, bytes) ← Alpha.decode 14 bytes
  let (orderBookId, bytes) ← decodeUInt 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (orderId, bytes) ← decodeUInt 8 bytes
  let (quantity, bytes) ← decodeUInt 8 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (timeInForce, bytes) ← decodeUInt 1 bytes
  let (openClose, bytes) ← decodeUInt 1 bytes
  let (clientAccount, bytes) ← Alpha.decode 16 bytes
  let (orderState, bytes) ← decodeUInt 1 bytes
  let (customerInfo, bytes) ← Alpha.decode 15 bytes
  let (exchangeInfo, bytes) ← Alpha.decode 32 bytes
  pure ({ timestampNanoseconds, orderToken, orderBookId, side, orderId, quantity, price, timeInForce, openClose, clientAccount, orderState, customerInfo, exchangeInfo }, bytes)

@[simp] theorem encode_length (message : OrderAccepted) : (encode message).length = 113 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, Side.encode_length]

theorem encode_length_pos (message : OrderAccepted) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderAccepted) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Side.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end OrderAccepted

/-- Mass Cancel Accepted: 26 bytes -/
structure MassCancelAccepted where
  timestampNanoseconds : BitVec 64
  orderToken : Alpha 14
  status : BitVec 32
  deriving DecidableEq, Repr

namespace MassCancelAccepted

def encode (message : MassCancelAccepted) : List UInt8 :=
  encodeUInt 8 message.timestampNanoseconds
    ++ Alpha.encode message.orderToken
    ++ encodeUInt 4 message.status

def decode (bytes : List UInt8) : Option (MassCancelAccepted × List UInt8) := do
  let (timestampNanoseconds, bytes) ← decodeUInt 8 bytes
  let (orderToken, bytes) ← Alpha.decode 14 bytes
  let (status, bytes) ← decodeUInt 4 bytes
  pure ({ timestampNanoseconds, orderToken, status }, bytes)

@[simp] theorem encode_length (message : MassCancelAccepted) : (encode message).length = 26 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : MassCancelAccepted) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MassCancelAccepted) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end MassCancelAccepted

/-- Order Rejected: 26 bytes -/
structure OrderRejected where
  timestampNanoseconds : BitVec 64
  orderToken : Alpha 14
  rejectCode : BitVec 32
  deriving DecidableEq, Repr

namespace OrderRejected

def encode (message : OrderRejected) : List UInt8 :=
  encodeUInt 8 message.timestampNanoseconds
    ++ Alpha.encode message.orderToken
    ++ encodeUInt 4 message.rejectCode

def decode (bytes : List UInt8) : Option (OrderRejected × List UInt8) := do
  let (timestampNanoseconds, bytes) ← decodeUInt 8 bytes
  let (orderToken, bytes) ← Alpha.decode 14 bytes
  let (rejectCode, bytes) ← decodeUInt 4 bytes
  pure ({ timestampNanoseconds, orderToken, rejectCode }, bytes)

@[simp] theorem encode_length (message : OrderRejected) : (encode message).length = 26 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : OrderRejected) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderRejected) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end OrderRejected

/-- Order Replaced: 127 bytes -/
structure OrderReplaced where
  timestampNanoseconds : BitVec 64
  replacementOrderToken : Alpha 14
  previousOrderToken : Alpha 14
  orderBookId : BitVec 32
  side : Side
  orderId : BitVec 64
  quantity : BitVec 64
  price : BitVec 32
  timeInForce : BitVec 8
  openClose : BitVec 8
  clientAccount : Alpha 16
  orderState : BitVec 8
  customerInfo : Alpha 15
  exchangeInfo : Alpha 32
  deriving DecidableEq, Repr

namespace OrderReplaced

def encode (message : OrderReplaced) : List UInt8 :=
  encodeUInt 8 message.timestampNanoseconds
    ++ Alpha.encode message.replacementOrderToken
    ++ Alpha.encode message.previousOrderToken
    ++ encodeUInt 4 message.orderBookId
    ++ Side.encode message.side
    ++ encodeUInt 8 message.orderId
    ++ encodeUInt 8 message.quantity
    ++ encodeUInt 4 message.price
    ++ encodeUInt 1 message.timeInForce
    ++ encodeUInt 1 message.openClose
    ++ Alpha.encode message.clientAccount
    ++ encodeUInt 1 message.orderState
    ++ Alpha.encode message.customerInfo
    ++ Alpha.encode message.exchangeInfo

def decode (bytes : List UInt8) : Option (OrderReplaced × List UInt8) := do
  let (timestampNanoseconds, bytes) ← decodeUInt 8 bytes
  let (replacementOrderToken, bytes) ← Alpha.decode 14 bytes
  let (previousOrderToken, bytes) ← Alpha.decode 14 bytes
  let (orderBookId, bytes) ← decodeUInt 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (orderId, bytes) ← decodeUInt 8 bytes
  let (quantity, bytes) ← decodeUInt 8 bytes
  let (price, bytes) ← decodeUInt 4 bytes
  let (timeInForce, bytes) ← decodeUInt 1 bytes
  let (openClose, bytes) ← decodeUInt 1 bytes
  let (clientAccount, bytes) ← Alpha.decode 16 bytes
  let (orderState, bytes) ← decodeUInt 1 bytes
  let (customerInfo, bytes) ← Alpha.decode 15 bytes
  let (exchangeInfo, bytes) ← Alpha.decode 32 bytes
  pure ({ timestampNanoseconds, replacementOrderToken, previousOrderToken, orderBookId, side, orderId, quantity, price, timeInForce, openClose, clientAccount, orderState, customerInfo, exchangeInfo }, bytes)

@[simp] theorem encode_length (message : OrderReplaced) : (encode message).length = 127 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, Side.encode_length]

theorem encode_length_pos (message : OrderReplaced) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderReplaced) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Side.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end OrderReplaced

/-- Order Canceled: 36 bytes -/
structure OrderCanceled where
  timestampNanoseconds : BitVec 64
  orderToken : Alpha 14
  orderBookId : BitVec 32
  side : Side
  orderId : BitVec 64
  cancelReason : BitVec 8
  deriving DecidableEq, Repr

namespace OrderCanceled

def encode (message : OrderCanceled) : List UInt8 :=
  encodeUInt 8 message.timestampNanoseconds
    ++ Alpha.encode message.orderToken
    ++ encodeUInt 4 message.orderBookId
    ++ Side.encode message.side
    ++ encodeUInt 8 message.orderId
    ++ encodeUInt 1 message.cancelReason

def decode (bytes : List UInt8) : Option (OrderCanceled × List UInt8) := do
  let (timestampNanoseconds, bytes) ← decodeUInt 8 bytes
  let (orderToken, bytes) ← Alpha.decode 14 bytes
  let (orderBookId, bytes) ← decodeUInt 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (orderId, bytes) ← decodeUInt 8 bytes
  let (cancelReason, bytes) ← decodeUInt 1 bytes
  pure ({ timestampNanoseconds, orderToken, orderBookId, side, orderId, cancelReason }, bytes)

@[simp] theorem encode_length (message : OrderCanceled) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length, Side.encode_length]

theorem encode_length_pos (message : OrderCanceled) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderCanceled) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Side.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end OrderCanceled

/-- Order Executed: 51 bytes -/
structure OrderExecuted where
  timestampNanoseconds : BitVec 64
  orderToken : Alpha 14
  orderBookId : BitVec 32
  tradedQuantity : BitVec 64
  tradePrice : BitVec 32
  matchId : BitVec 64
  comboGroupId : BitVec 32
  dealSource : BitVec 8
  deriving DecidableEq, Repr

namespace OrderExecuted

def encode (message : OrderExecuted) : List UInt8 :=
  encodeUInt 8 message.timestampNanoseconds
    ++ Alpha.encode message.orderToken
    ++ encodeUInt 4 message.orderBookId
    ++ encodeUInt 8 message.tradedQuantity
    ++ encodeUInt 4 message.tradePrice
    ++ encodeUInt 8 message.matchId
    ++ encodeUInt 4 message.comboGroupId
    ++ encodeUInt 1 message.dealSource

def decode (bytes : List UInt8) : Option (OrderExecuted × List UInt8) := do
  let (timestampNanoseconds, bytes) ← decodeUInt 8 bytes
  let (orderToken, bytes) ← Alpha.decode 14 bytes
  let (orderBookId, bytes) ← decodeUInt 4 bytes
  let (tradedQuantity, bytes) ← decodeUInt 8 bytes
  let (tradePrice, bytes) ← decodeUInt 4 bytes
  let (matchId, bytes) ← decodeUInt 8 bytes
  let (comboGroupId, bytes) ← decodeUInt 4 bytes
  let (dealSource, bytes) ← decodeUInt 1 bytes
  pure ({ timestampNanoseconds, orderToken, orderBookId, tradedQuantity, tradePrice, matchId, comboGroupId, dealSource }, bytes)

@[simp] theorem encode_length (message : OrderExecuted) : (encode message).length = 51 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : OrderExecuted) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderExecuted) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end OrderExecuted

/-- Any Sequenced Message, selected by Sequenced Message Type -/
inductive SequencedMessage where
  | orderAccepted (message : OrderAccepted) -- 'A' 0x41
  | massCancelAccepted (message : MassCancelAccepted) -- 'M' 0x4D
  | orderRejected (message : OrderRejected) -- 'J' 0x4A
  | orderReplaced (message : OrderReplaced) -- 'U' 0x55
  | orderCanceled (message : OrderCanceled) -- 'C' 0x43
  | orderExecuted (message : OrderExecuted) -- 'E' 0x45
  deriving DecidableEq, Repr

namespace SequencedMessage

/-- The Sequenced Message Type each message is sent under -/
def tag : SequencedMessage → BitVec 8
  | .orderAccepted _ => 65
  | .massCancelAccepted _ => 77
  | .orderRejected _ => 74
  | .orderReplaced _ => 85
  | .orderCanceled _ => 67
  | .orderExecuted _ => 69

def encode : SequencedMessage → List UInt8
  | .orderAccepted message => OrderAccepted.encode message
  | .massCancelAccepted message => MassCancelAccepted.encode message
  | .orderRejected message => OrderRejected.encode message
  | .orderReplaced message => OrderReplaced.encode message
  | .orderCanceled message => OrderCanceled.encode message
  | .orderExecuted message => OrderExecuted.encode message

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (SequencedMessage × List UInt8) :=
  if tag = 65 then (OrderAccepted.decode bytes).map fun (message, rest) => (.orderAccepted message, rest)
  else if tag = 77 then (MassCancelAccepted.decode bytes).map fun (message, rest) => (.massCancelAccepted message, rest)
  else if tag = 74 then (OrderRejected.decode bytes).map fun (message, rest) => (.orderRejected message, rest)
  else if tag = 85 then (OrderReplaced.decode bytes).map fun (message, rest) => (.orderReplaced message, rest)
  else if tag = 67 then (OrderCanceled.decode bytes).map fun (message, rest) => (.orderCanceled message, rest)
  else if tag = 69 then (OrderExecuted.decode bytes).map fun (message, rest) => (.orderExecuted message, rest)
  else none

@[simp] theorem decode_encode (message : SequencedMessage) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end SequencedMessage

/-- Sequenced Data Packet -/
structure SequencedDataPacket where
  sequencedMessage : SequencedMessage
  deriving DecidableEq, Repr

namespace SequencedDataPacket

def encode (message : SequencedDataPacket) : List UInt8 :=
  encodeUInt 1 (SequencedMessage.tag message.sequencedMessage)
    ++ SequencedMessage.encode message.sequencedMessage

def decode (bytes : List UInt8) : Option (SequencedDataPacket × List UInt8) := do
  let (sequencedMessageType, bytes) ← decodeUInt 1 bytes
  let (sequencedMessage, bytes) ← SequencedMessage.decode sequencedMessageType bytes
  pure ({ sequencedMessage }, bytes)

theorem encode_length_pos (message : SequencedDataPacket) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SequencedDataPacket) : (encode message).length ≤ 128 := by
  unfold encode
  cases message.sequencedMessage with
  | orderAccepted inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, OrderAccepted.encode_length]
    omega
  | massCancelAccepted inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, MassCancelAccepted.encode_length]
    omega
  | orderRejected inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, OrderRejected.encode_length]
    omega
  | orderReplaced inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, OrderReplaced.encode_length]
    omega
  | orderCanceled inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, OrderCanceled.encode_length]
    omega
  | orderExecuted inner =>
    simp only [SequencedMessage.encode, List.length_append, encodeUInt_length, OrderExecuted.encode_length]
    omega

@[simp] theorem decode_encode (message : SequencedDataPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [SequencedMessage.decode_encode, Option.bind_some]
  rfl

end SequencedDataPacket

/-- Server Heartbeat: 0 bytes -/
structure ServerHeartbeat where
  deriving DecidableEq, Repr

namespace ServerHeartbeat

def encode (_ : ServerHeartbeat) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (ServerHeartbeat × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : ServerHeartbeat) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : ServerHeartbeat) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end ServerHeartbeat

/-- End Of Session: 0 bytes -/
structure EndOfSession where
  deriving DecidableEq, Repr

namespace EndOfSession

def encode (_ : EndOfSession) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (EndOfSession × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : EndOfSession) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : EndOfSession) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end EndOfSession

/-- Any Server Payload, selected by Server Packet Type -/
inductive ServerPayload where
  | debugPacket (message : DebugPacket) -- '+' 0x2B
  | loginAcceptedPacket (message : LoginAcceptedPacket) -- 'A' 0x41
  | loginRejectedPacket (message : LoginRejectedPacket) -- 'J' 0x4A
  | sequencedDataPacket (message : SequencedDataPacket) -- 'S' 0x53
  | serverHeartbeat (message : ServerHeartbeat) -- 'H' 0x48
  | endOfSession (message : EndOfSession) -- 'Z' 0x5A
  deriving DecidableEq, Repr

namespace ServerPayload

/-- The Server Packet Type each message is sent under -/
def tag : ServerPayload → BitVec 8
  | .debugPacket _ => 43
  | .loginAcceptedPacket _ => 65
  | .loginRejectedPacket _ => 74
  | .sequencedDataPacket _ => 83
  | .serverHeartbeat _ => 72
  | .endOfSession _ => 90

def encode : ServerPayload → List UInt8
  | .debugPacket message => DebugPacket.encode message
  | .loginAcceptedPacket message => LoginAcceptedPacket.encode message
  | .loginRejectedPacket message => LoginRejectedPacket.encode message
  | .sequencedDataPacket message => SequencedDataPacket.encode message
  | .serverHeartbeat message => ServerHeartbeat.encode message
  | .endOfSession message => EndOfSession.encode message

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (ServerPayload × List UInt8) :=
  if tag = 43 then (DebugPacket.decode bytes).map fun (message, rest) => (.debugPacket message, rest)
  else if tag = 65 then (LoginAcceptedPacket.decode bytes).map fun (message, rest) => (.loginAcceptedPacket message, rest)
  else if tag = 74 then (LoginRejectedPacket.decode bytes).map fun (message, rest) => (.loginRejectedPacket message, rest)
  else if tag = 83 then (SequencedDataPacket.decode bytes).map fun (message, rest) => (.sequencedDataPacket message, rest)
  else if tag = 72 then (ServerHeartbeat.decode bytes).map fun (message, rest) => (.serverHeartbeat message, rest)
  else if tag = 90 then (EndOfSession.decode bytes).map fun (message, rest) => (.endOfSession message, rest)
  else none

@[simp] theorem decode_encode (message : ServerPayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end ServerPayload

/-- Server Soup Bin Tcp Packet -/
structure ServerSoupBinTcpPacket where
  serverPayload : ServerPayload
  deriving DecidableEq, Repr

namespace ServerSoupBinTcpPacket

def encodeBody (message : ServerSoupBinTcpPacket) : List UInt8 :=
  encodeUInt 1 (ServerPayload.tag message.serverPayload)
    ++ ServerPayload.encode message.serverPayload

def decodeBody (bytes : List UInt8) : Option (ServerSoupBinTcpPacket × List UInt8) := do
  let (serverPacketType, bytes) ← decodeUInt 1 bytes
  let (serverPayload, bytes) ← ServerPayload.decode serverPacketType bytes
  pure ({ serverPayload }, bytes)

theorem decodeBody_encodeBody (message : ServerSoupBinTcpPacket) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [ServerPayload.decode_encode, Option.bind_some]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : ServerSoupBinTcpPacket) : (encodeBody message).length + 0 < 256 ^ 2 := by
  unfold encodeBody
  cases message.serverPayload with
  | debugPacket inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUInt_length, DebugPacket.encode_length]
    omega
  | loginAcceptedPacket inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUInt_length, LoginAcceptedPacket.encode_length]
    omega
  | loginRejectedPacket inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUInt_length, LoginRejectedPacket.encode_length]
    omega
  | sequencedDataPacket inner =>
    have bound_inner := SequencedDataPacket.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUInt_length]
    omega
  | serverHeartbeat inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUInt_length, ServerHeartbeat.encode_length]
    omega
  | endOfSession inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUInt_length, EndOfSession.encode_length]
    omega

/-- Size rule: Packet Length counts the bytes after it, so it is written from the body and checked on decode -/
def encode : ServerSoupBinTcpPacket → List UInt8 :=
  encodeFramed 2 0 encodeBody

def decode : List UInt8 → Option (ServerSoupBinTcpPacket × List UInt8) :=
  decodeFramed 2 0 decodeBody

@[simp] theorem decode_encode (message : ServerSoupBinTcpPacket) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramed_encodeFramed 2 0 encodeBody decodeBody decodeBody_encodeBody encodeBody_length_lt message rest

theorem encode_length_pos (message : ServerSoupBinTcpPacket) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramed_length]
  omega

end ServerSoupBinTcpPacket

/-- Server Packet -/
structure ServerPacket where
  serverSoupBinTcpPacket : List ServerSoupBinTcpPacket
  deriving DecidableEq, Repr

namespace ServerPacket

def encode (message : ServerPacket) : List UInt8 :=
  encodeMany ServerSoupBinTcpPacket.encode message.serverSoupBinTcpPacket

def decode (bytes : List UInt8) : Option ServerPacket := do
  let serverSoupBinTcpPacket ← decodeAll ServerSoupBinTcpPacket.decode bytes.length bytes
  pure { serverSoupBinTcpPacket }

theorem decode_encode (message : ServerPacket) : decode (encode message) = some message := by
  unfold decode encode
  simp only [Option.bind_eq_bind]
  rw [decodeAll_encodeMany ServerSoupBinTcpPacket.encode ServerSoupBinTcpPacket.decode ServerSoupBinTcpPacket.decode_encode ServerSoupBinTcpPacket.encode_length_pos message.serverSoupBinTcpPacket _ (encodeMany_length_ge ServerSoupBinTcpPacket.encode ServerSoupBinTcpPacket.encode_length_pos message.serverSoupBinTcpPacket), Option.bind_some]
  rfl

end ServerPacket

end Omi.JpxOsederivativesGeniuminetOuchV50Server
