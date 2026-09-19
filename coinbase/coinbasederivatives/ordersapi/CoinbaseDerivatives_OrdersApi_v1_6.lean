import Omi.Wire

/-!
# Coinbase Orders Api v1.6

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Flags is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Session Message and Order Message carry no fields of their own, so their messages are dispatched as one, keyed on Schema Id and Template Id.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.CoinbaseCoinbasederivativesOrdersapiSbeV16

/-- Logon Message: 49 bytes -/
structure LogonMessage where
  username : Alpha 16
  password : Alpha 32
  resetSeqNum : BitVec 8
  deriving DecidableEq, Repr

namespace LogonMessage

def encode (message : LogonMessage) : List UInt8 :=
  Alpha.encode message.username
    ++ (Alpha.encode message.password
    ++ (encodeUInt 1 message.resetSeqNum))

def decode (bytes : List UInt8) : Option (LogonMessage × List UInt8) := do
  let (username, bytes) ← Alpha.decode 16 bytes
  let (password, bytes) ← Alpha.decode 32 bytes
  let (resetSeqNum, bytes) ← decodeUInt 1 bytes
  pure ({ username, password, resetSeqNum }, bytes)

@[simp] theorem encode_length (message : LogonMessage) : (encode message).length = 49 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : LogonMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LogonMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end LogonMessage

/-- Logon Conf Message: 4 bytes -/
structure LogonConfMessage where
  heartbeatIntervalSeconds : BitVec 32
  deriving DecidableEq, Repr

namespace LogonConfMessage

def encode (message : LogonConfMessage) : List UInt8 :=
  encodeUIntLE 4 message.heartbeatIntervalSeconds

def decode (bytes : List UInt8) : Option (LogonConfMessage × List UInt8) := do
  let (heartbeatIntervalSeconds, bytes) ← decodeUIntLE 4 bytes
  pure ({ heartbeatIntervalSeconds }, bytes)

@[simp] theorem encode_length (message : LogonConfMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : LogonConfMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LogonConfMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end LogonConfMessage

/-- Logout Message: 64 bytes -/
structure LogoutMessage where
  reason : Alpha 64
  deriving DecidableEq, Repr

namespace LogoutMessage

def encode (message : LogoutMessage) : List UInt8 :=
  Alpha.encode message.reason

def decode (bytes : List UInt8) : Option (LogoutMessage × List UInt8) := do
  let (reason, bytes) ← Alpha.decode 64 bytes
  pure ({ reason }, bytes)

@[simp] theorem encode_length (message : LogoutMessage) : (encode message).length = 64 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : LogoutMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LogoutMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end LogoutMessage

/-- Logged Out Message: 64 bytes -/
structure LoggedOutMessage where
  reason : Alpha 64
  deriving DecidableEq, Repr

namespace LoggedOutMessage

def encode (message : LoggedOutMessage) : List UInt8 :=
  Alpha.encode message.reason

def decode (bytes : List UInt8) : Option (LoggedOutMessage × List UInt8) := do
  let (reason, bytes) ← Alpha.decode 64 bytes
  pure ({ reason }, bytes)

@[simp] theorem encode_length (message : LoggedOutMessage) : (encode message).length = 64 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : LoggedOutMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LoggedOutMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end LoggedOutMessage

/-- Heartbeat Message: 8 bytes -/
structure HeartbeatMessage where
  correlationId : BitVec 64
  deriving DecidableEq, Repr

namespace HeartbeatMessage

def encode (message : HeartbeatMessage) : List UInt8 :=
  encodeUIntLE 8 message.correlationId

def decode (bytes : List UInt8) : Option (HeartbeatMessage × List UInt8) := do
  let (correlationId, bytes) ← decodeUIntLE 8 bytes
  pure ({ correlationId }, bytes)

@[simp] theorem encode_length (message : HeartbeatMessage) : (encode message).length = 8 := by
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : HeartbeatMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : HeartbeatMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end HeartbeatMessage

/-- Test Request Message: 8 bytes -/
structure TestRequestMessage where
  correlationId : BitVec 64
  deriving DecidableEq, Repr

namespace TestRequestMessage

def encode (message : TestRequestMessage) : List UInt8 :=
  encodeUIntLE 8 message.correlationId

def decode (bytes : List UInt8) : Option (TestRequestMessage × List UInt8) := do
  let (correlationId, bytes) ← decodeUIntLE 8 bytes
  pure ({ correlationId }, bytes)

@[simp] theorem encode_length (message : TestRequestMessage) : (encode message).length = 8 := by
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : TestRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TestRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TestRequestMessage

/-- Resend Request Message: 8 bytes -/
structure ResendRequestMessage where
  fromSequenceNumber : BitVec 32
  toSequenceNumber : BitVec 32
  deriving DecidableEq, Repr

namespace ResendRequestMessage

def encode (message : ResendRequestMessage) : List UInt8 :=
  encodeUIntLE 4 message.fromSequenceNumber
    ++ (encodeUIntLE 4 message.toSequenceNumber)

def decode (bytes : List UInt8) : Option (ResendRequestMessage × List UInt8) := do
  let (fromSequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (toSequenceNumber, bytes) ← decodeUIntLE 4 bytes
  pure ({ fromSequenceNumber, toSequenceNumber }, bytes)

@[simp] theorem encode_length (message : ResendRequestMessage) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : ResendRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ResendRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end ResendRequestMessage

/-- Gap Fill Message: 8 bytes -/
structure GapFillMessage where
  newSequenceNumber : BitVec 32
  gapFillPadding : BitVec 32
  deriving DecidableEq, Repr

namespace GapFillMessage

def encode (message : GapFillMessage) : List UInt8 :=
  encodeUIntLE 4 message.newSequenceNumber
    ++ (encodeUIntLE 4 message.gapFillPadding)

def decode (bytes : List UInt8) : Option (GapFillMessage × List UInt8) := do
  let (newSequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (gapFillPadding, bytes) ← decodeUIntLE 4 bytes
  pure ({ newSequenceNumber, gapFillPadding }, bytes)

@[simp] theorem encode_length (message : GapFillMessage) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : GapFillMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : GapFillMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end GapFillMessage

/-- Data -/
structure Data where
  dataValue : Bounded 1 UInt8
  deriving DecidableEq, Repr

namespace Data

def encode (message : Data) : List UInt8 :=
  encodeUInt 1 (BitVec.ofNat (8 * 1) message.dataValue.val.length)
    ++ (encodeMany Byte.encode message.dataValue.val)

def decode (bytes : List UInt8) : Option (Data × List UInt8) := do
  let (dataLength, bytes) ← decodeUInt 1 bytes
  let (dataValue_, bytes) ← decodeMany Byte.decode dataLength.toNat bytes
  if fits_dataValue : dataValue_.length < 256 ^ 1 then
    pure ({ dataValue := ⟨dataValue_, fits_dataValue⟩ }, bytes)
  else none

theorem encode_length_pos (message : Data) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : Data) : (encode message).length ≤ 256 := by
  have bound_dataValue := message.dataValue.length_lt
  unfold encode
  simp only [List.length_append, encodeUInt_length, encodeMany_length_const Byte.encode 1 Byte.encode_length]
  omega

@[simp] theorem decode_encode (message : Data) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 Byte.encode Byte.decode Byte.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.dataValue.length_lt]
  rfl

end Data

/-- Ping Message -/
structure PingMessage where
  correlationId : BitVec 64
  requestTime : BitVec 64
  data : Data
  deriving DecidableEq, Repr

namespace PingMessage

def encode (message : PingMessage) : List UInt8 :=
  encodeUIntLE 8 message.correlationId
    ++ (encodeUIntLE 8 message.requestTime
    ++ (Data.encode message.data))

def decode (bytes : List UInt8) : Option (PingMessage × List UInt8) := do
  let (correlationId, bytes) ← decodeUIntLE 8 bytes
  let (requestTime, bytes) ← decodeUIntLE 8 bytes
  let (data, bytes) ← Data.decode bytes
  pure ({ correlationId, requestTime, data }, bytes)

theorem encode_length_pos (message : PingMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : PingMessage) : (encode message).length ≤ 272 := by
  have bound_data := Data.encode_length_le message.data
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
  omega

@[simp] theorem decode_encode (message : PingMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Data.decode_encode, some_bind]
  rfl

end PingMessage

/-- Pong Message -/
structure PongMessage where
  correlationId : BitVec 64
  requestTime : BitVec 64
  serverTime : BitVec 64
  tradingInstrumentStatus : BitVec 8
  data : Data
  deriving DecidableEq, Repr

namespace PongMessage

def encode (message : PongMessage) : List UInt8 :=
  encodeUIntLE 8 message.correlationId
    ++ (encodeUIntLE 8 message.requestTime
    ++ (encodeUIntLE 8 message.serverTime
    ++ (encodeUInt 1 message.tradingInstrumentStatus
    ++ (Data.encode message.data))))

def decode (bytes : List UInt8) : Option (PongMessage × List UInt8) := do
  let (correlationId, bytes) ← decodeUIntLE 8 bytes
  let (requestTime, bytes) ← decodeUIntLE 8 bytes
  let (serverTime, bytes) ← decodeUIntLE 8 bytes
  let (tradingInstrumentStatus, bytes) ← decodeUInt 1 bytes
  let (data, bytes) ← Data.decode bytes
  pure ({ correlationId, requestTime, serverTime, tradingInstrumentStatus, data }, bytes)

theorem encode_length_pos (message : PongMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : PongMessage) : (encode message).length ≤ 281 := by
  have bound_data := Data.encode_length_le message.data
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length]
  omega

@[simp] theorem decode_encode (message : PongMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Data.decode_encode, some_bind]
  rfl

end PongMessage

/-- Instrument Info Request Message: 8 bytes -/
structure InstrumentInfoRequestMessage where
  correlationId : BitVec 64
  deriving DecidableEq, Repr

namespace InstrumentInfoRequestMessage

def encode (message : InstrumentInfoRequestMessage) : List UInt8 :=
  encodeUIntLE 8 message.correlationId

def decode (bytes : List UInt8) : Option (InstrumentInfoRequestMessage × List UInt8) := do
  let (correlationId, bytes) ← decodeUIntLE 8 bytes
  pure ({ correlationId }, bytes)

@[simp] theorem encode_length (message : InstrumentInfoRequestMessage) : (encode message).length = 8 := by
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : InstrumentInfoRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstrumentInfoRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end InstrumentInfoRequestMessage

/-- Instrument Info Message: 48 bytes -/
structure InstrumentInfoMessage where
  correlationId : BitVec 64
  instrumentId : BitVec 32
  securityType : BitVec 8
  instrumentStatus : BitVec 8
  isLastMessage : BitVec 8
  reservedByte : BitVec 8
  symbol : Alpha 32
  deriving DecidableEq, Repr

namespace InstrumentInfoMessage

def encode (message : InstrumentInfoMessage) : List UInt8 :=
  encodeUIntLE 8 message.correlationId
    ++ (encodeUIntLE 4 message.instrumentId
    ++ (encodeUInt 1 message.securityType
    ++ (encodeUInt 1 message.instrumentStatus
    ++ (encodeUInt 1 message.isLastMessage
    ++ (encodeUInt 1 message.reservedByte
    ++ (Alpha.encode message.symbol))))))

def decode (bytes : List UInt8) : Option (InstrumentInfoMessage × List UInt8) := do
  let (correlationId, bytes) ← decodeUIntLE 8 bytes
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (securityType, bytes) ← decodeUInt 1 bytes
  let (instrumentStatus, bytes) ← decodeUInt 1 bytes
  let (isLastMessage, bytes) ← decodeUInt 1 bytes
  let (reservedByte, bytes) ← decodeUInt 1 bytes
  let (symbol, bytes) ← Alpha.decode 32 bytes
  pure ({ correlationId, instrumentId, securityType, instrumentStatus, isLastMessage, reservedByte, symbol }, bytes)

@[simp] theorem encode_length (message : InstrumentInfoMessage) : (encode message).length = 48 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : InstrumentInfoMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstrumentInfoMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
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

end InstrumentInfoMessage

/-- Set Account Message: 24 bytes -/
structure SetAccountMessage where
  correlationId : BitVec 64
  account : Alpha 16
  deriving DecidableEq, Repr

namespace SetAccountMessage

def encode (message : SetAccountMessage) : List UInt8 :=
  encodeUIntLE 8 message.correlationId
    ++ (Alpha.encode message.account)

def decode (bytes : List UInt8) : Option (SetAccountMessage × List UInt8) := do
  let (correlationId, bytes) ← decodeUIntLE 8 bytes
  let (account, bytes) ← Alpha.decode 16 bytes
  pure ({ correlationId, account }, bytes)

@[simp] theorem encode_length (message : SetAccountMessage) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : SetAccountMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SetAccountMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SetAccountMessage

/-- Set Trader Message: 24 bytes -/
structure SetTraderMessage where
  correlationId : BitVec 64
  trader : Alpha 16
  deriving DecidableEq, Repr

namespace SetTraderMessage

def encode (message : SetTraderMessage) : List UInt8 :=
  encodeUIntLE 8 message.correlationId
    ++ (Alpha.encode message.trader)

def decode (bytes : List UInt8) : Option (SetTraderMessage × List UInt8) := do
  let (correlationId, bytes) ← decodeUIntLE 8 bytes
  let (trader, bytes) ← Alpha.decode 16 bytes
  pure ({ correlationId, trader }, bytes)

@[simp] theorem encode_length (message : SetTraderMessage) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : SetTraderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SetTraderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SetTraderMessage

/-- Set Ack Message: 8 bytes -/
structure SetAckMessage where
  correlationId : BitVec 64
  deriving DecidableEq, Repr

namespace SetAckMessage

def encode (message : SetAckMessage) : List UInt8 :=
  encodeUIntLE 8 message.correlationId

def decode (bytes : List UInt8) : Option (SetAckMessage × List UInt8) := do
  let (correlationId, bytes) ← decodeUIntLE 8 bytes
  pure ({ correlationId }, bytes)

@[simp] theorem encode_length (message : SetAckMessage) : (encode message).length = 8 := by
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : SetAckMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SetAckMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SetAckMessage

/-- New Order Message: 36 bytes -/
structure NewOrderMessage where
  clientOrderId : BitVec 64
  correlationId : BitVec 64
  limitPrice : BitVec 64
  quantity : BitVec 32
  instrumentId : BitVec 32
  side : BitVec 8
  flags : BitVec 8
  goodTilDate : BitVec 16
  deriving DecidableEq, Repr

namespace NewOrderMessage

def encode (message : NewOrderMessage) : List UInt8 :=
  encodeUIntLE 8 message.clientOrderId
    ++ (encodeUIntLE 8 message.correlationId
    ++ (encodeUIntLE 8 message.limitPrice
    ++ (encodeUIntLE 4 message.quantity
    ++ (encodeUIntLE 4 message.instrumentId
    ++ (encodeUInt 1 message.side
    ++ (encodeUIntLE 1 message.flags
    ++ (encodeUIntLE 2 message.goodTilDate)))))))

def decode (bytes : List UInt8) : Option (NewOrderMessage × List UInt8) := do
  let (clientOrderId, bytes) ← decodeUIntLE 8 bytes
  let (correlationId, bytes) ← decodeUIntLE 8 bytes
  let (limitPrice, bytes) ← decodeUIntLE 8 bytes
  let (quantity, bytes) ← decodeUIntLE 4 bytes
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (flags, bytes) ← decodeUIntLE 1 bytes
  let (goodTilDate, bytes) ← decodeUIntLE 2 bytes
  pure ({ clientOrderId, correlationId, limitPrice, quantity, instrumentId, side, flags, goodTilDate }, bytes)

@[simp] theorem encode_length (message : NewOrderMessage) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : NewOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NewOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end NewOrderMessage

/-- New Ioc Order Message: 37 bytes -/
structure NewIocOrderMessage where
  clientOrderId : BitVec 64
  correlationId : BitVec 64
  limitPrice : BitVec 64
  quantity : BitVec 32
  minQty : BitVec 32
  instrumentId : BitVec 32
  side : BitVec 8
  deriving DecidableEq, Repr

namespace NewIocOrderMessage

def encode (message : NewIocOrderMessage) : List UInt8 :=
  encodeUIntLE 8 message.clientOrderId
    ++ (encodeUIntLE 8 message.correlationId
    ++ (encodeUIntLE 8 message.limitPrice
    ++ (encodeUIntLE 4 message.quantity
    ++ (encodeUIntLE 4 message.minQty
    ++ (encodeUIntLE 4 message.instrumentId
    ++ (encodeUInt 1 message.side))))))

def decode (bytes : List UInt8) : Option (NewIocOrderMessage × List UInt8) := do
  let (clientOrderId, bytes) ← decodeUIntLE 8 bytes
  let (correlationId, bytes) ← decodeUIntLE 8 bytes
  let (limitPrice, bytes) ← decodeUIntLE 8 bytes
  let (quantity, bytes) ← decodeUIntLE 4 bytes
  let (minQty, bytes) ← decodeUIntLE 4 bytes
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  pure ({ clientOrderId, correlationId, limitPrice, quantity, minQty, instrumentId, side }, bytes)

@[simp] theorem encode_length (message : NewIocOrderMessage) : (encode message).length = 37 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : NewIocOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NewIocOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end NewIocOrderMessage

/-- Order Entered Message: 48 bytes -/
structure OrderEnteredMessage where
  timestamp : BitVec 64
  execId : BitVec 64
  clientOrderId : BitVec 64
  correlationId : BitVec 64
  orderId : BitVec 64
  receiveTime : BitVec 64
  deriving DecidableEq, Repr

namespace OrderEnteredMessage

def encode (message : OrderEnteredMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.execId
    ++ (encodeUIntLE 8 message.clientOrderId
    ++ (encodeUIntLE 8 message.correlationId
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.receiveTime)))))

def decode (bytes : List UInt8) : Option (OrderEnteredMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  let (clientOrderId, bytes) ← decodeUIntLE 8 bytes
  let (correlationId, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (receiveTime, bytes) ← decodeUIntLE 8 bytes
  pure ({ timestamp, execId, clientOrderId, correlationId, orderId, receiveTime }, bytes)

@[simp] theorem encode_length (message : OrderEnteredMessage) : (encode message).length = 48 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : OrderEnteredMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderEnteredMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OrderEnteredMessage

/-- Replace Order Message: 35 bytes -/
structure ReplaceOrderMessage where
  clientOrderId : BitVec 64
  correlationId : BitVec 64
  newLimitPrice : BitVec 64
  newQuantity : BitVec 32
  instrumentId : BitVec 32
  goodTilDate : BitVec 16
  timeInForce : BitVec 8
  deriving DecidableEq, Repr

namespace ReplaceOrderMessage

def encode (message : ReplaceOrderMessage) : List UInt8 :=
  encodeUIntLE 8 message.clientOrderId
    ++ (encodeUIntLE 8 message.correlationId
    ++ (encodeUIntLE 8 message.newLimitPrice
    ++ (encodeUIntLE 4 message.newQuantity
    ++ (encodeUIntLE 4 message.instrumentId
    ++ (encodeUIntLE 2 message.goodTilDate
    ++ (encodeUInt 1 message.timeInForce))))))

def decode (bytes : List UInt8) : Option (ReplaceOrderMessage × List UInt8) := do
  let (clientOrderId, bytes) ← decodeUIntLE 8 bytes
  let (correlationId, bytes) ← decodeUIntLE 8 bytes
  let (newLimitPrice, bytes) ← decodeUIntLE 8 bytes
  let (newQuantity, bytes) ← decodeUIntLE 4 bytes
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (goodTilDate, bytes) ← decodeUIntLE 2 bytes
  let (timeInForce, bytes) ← decodeUInt 1 bytes
  pure ({ clientOrderId, correlationId, newLimitPrice, newQuantity, instrumentId, goodTilDate, timeInForce }, bytes)

@[simp] theorem encode_length (message : ReplaceOrderMessage) : (encode message).length = 35 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : ReplaceOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ReplaceOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ReplaceOrderMessage

/-- Obsolete Stream Order Message: 41 bytes -/
structure ObsoleteStreamOrderMessage where
  clientOrderId : BitVec 64
  correlationId : BitVec 64
  lastProcessedFillId : BitVec 64
  limitPrice : BitVec 64
  quantity : BitVec 32
  instrumentId : BitVec 32
  side : BitVec 8
  deriving DecidableEq, Repr

namespace ObsoleteStreamOrderMessage

def encode (message : ObsoleteStreamOrderMessage) : List UInt8 :=
  encodeUIntLE 8 message.clientOrderId
    ++ (encodeUIntLE 8 message.correlationId
    ++ (encodeUIntLE 8 message.lastProcessedFillId
    ++ (encodeUIntLE 8 message.limitPrice
    ++ (encodeUIntLE 4 message.quantity
    ++ (encodeUIntLE 4 message.instrumentId
    ++ (encodeUInt 1 message.side))))))

def decode (bytes : List UInt8) : Option (ObsoleteStreamOrderMessage × List UInt8) := do
  let (clientOrderId, bytes) ← decodeUIntLE 8 bytes
  let (correlationId, bytes) ← decodeUIntLE 8 bytes
  let (lastProcessedFillId, bytes) ← decodeUIntLE 8 bytes
  let (limitPrice, bytes) ← decodeUIntLE 8 bytes
  let (quantity, bytes) ← decodeUIntLE 4 bytes
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  pure ({ clientOrderId, correlationId, lastProcessedFillId, limitPrice, quantity, instrumentId, side }, bytes)

@[simp] theorem encode_length (message : ObsoleteStreamOrderMessage) : (encode message).length = 41 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : ObsoleteStreamOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ObsoleteStreamOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ObsoleteStreamOrderMessage

/-- Order Reject Message: 80 bytes -/
structure OrderRejectMessage where
  timestamp : BitVec 64
  clientOrderId : BitVec 64
  correlationId : BitVec 64
  orderIdOptional : BitVec 64
  orderRejectReason : BitVec 8
  orderRejectDetails : Alpha 47
  deriving DecidableEq, Repr

namespace OrderRejectMessage

def encode (message : OrderRejectMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.clientOrderId
    ++ (encodeUIntLE 8 message.correlationId
    ++ (encodeUIntLE 8 message.orderIdOptional
    ++ (encodeUInt 1 message.orderRejectReason
    ++ (Alpha.encode message.orderRejectDetails)))))

def decode (bytes : List UInt8) : Option (OrderRejectMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (clientOrderId, bytes) ← decodeUIntLE 8 bytes
  let (correlationId, bytes) ← decodeUIntLE 8 bytes
  let (orderIdOptional, bytes) ← decodeUIntLE 8 bytes
  let (orderRejectReason, bytes) ← decodeUInt 1 bytes
  let (orderRejectDetails, bytes) ← Alpha.decode 47 bytes
  pure ({ timestamp, clientOrderId, correlationId, orderIdOptional, orderRejectReason, orderRejectDetails }, bytes)

@[simp] theorem encode_length (message : OrderRejectMessage) : (encode message).length = 80 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : OrderRejectMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderRejectMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderRejectMessage

/-- Order Replaced Message: 60 bytes -/
structure OrderReplacedMessage where
  timestamp : BitVec 64
  execId : BitVec 64
  clientOrderId : BitVec 64
  correlationId : BitVec 64
  orderId : BitVec 64
  receiveTime : BitVec 64
  totalFilled : BitVec 32
  availableQty : BitVec 32
  instrumentId : BitVec 32
  deriving DecidableEq, Repr

namespace OrderReplacedMessage

def encode (message : OrderReplacedMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.execId
    ++ (encodeUIntLE 8 message.clientOrderId
    ++ (encodeUIntLE 8 message.correlationId
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.receiveTime
    ++ (encodeUIntLE 4 message.totalFilled
    ++ (encodeUIntLE 4 message.availableQty
    ++ (encodeUIntLE 4 message.instrumentId))))))))

def decode (bytes : List UInt8) : Option (OrderReplacedMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  let (clientOrderId, bytes) ← decodeUIntLE 8 bytes
  let (correlationId, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (receiveTime, bytes) ← decodeUIntLE 8 bytes
  let (totalFilled, bytes) ← decodeUIntLE 4 bytes
  let (availableQty, bytes) ← decodeUIntLE 4 bytes
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  pure ({ timestamp, execId, clientOrderId, correlationId, orderId, receiveTime, totalFilled, availableQty, instrumentId }, bytes)

@[simp] theorem encode_length (message : OrderReplacedMessage) : (encode message).length = 60 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : OrderReplacedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderReplacedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OrderReplacedMessage

/-- Cancel Order Message: 20 bytes -/
structure CancelOrderMessage where
  clientOrderId : BitVec 64
  correlationId : BitVec 64
  instrumentId : BitVec 32
  deriving DecidableEq, Repr

namespace CancelOrderMessage

def encode (message : CancelOrderMessage) : List UInt8 :=
  encodeUIntLE 8 message.clientOrderId
    ++ (encodeUIntLE 8 message.correlationId
    ++ (encodeUIntLE 4 message.instrumentId))

def decode (bytes : List UInt8) : Option (CancelOrderMessage × List UInt8) := do
  let (clientOrderId, bytes) ← decodeUIntLE 8 bytes
  let (correlationId, bytes) ← decodeUIntLE 8 bytes
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  pure ({ clientOrderId, correlationId, instrumentId }, bytes)

@[simp] theorem encode_length (message : CancelOrderMessage) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : CancelOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CancelOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end CancelOrderMessage

/-- Order Canceled Message: 57 bytes -/
structure OrderCanceledMessage where
  timestamp : BitVec 64
  execId : BitVec 64
  clientOrderId : BitVec 64
  correlationId : BitVec 64
  orderId : BitVec 64
  receiveTime : BitVec 64
  totalFilled : BitVec 32
  instrumentId : BitVec 32
  cancelReason : BitVec 8
  deriving DecidableEq, Repr

namespace OrderCanceledMessage

def encode (message : OrderCanceledMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.execId
    ++ (encodeUIntLE 8 message.clientOrderId
    ++ (encodeUIntLE 8 message.correlationId
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.receiveTime
    ++ (encodeUIntLE 4 message.totalFilled
    ++ (encodeUIntLE 4 message.instrumentId
    ++ (encodeUInt 1 message.cancelReason))))))))

def decode (bytes : List UInt8) : Option (OrderCanceledMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  let (clientOrderId, bytes) ← decodeUIntLE 8 bytes
  let (correlationId, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (receiveTime, bytes) ← decodeUIntLE 8 bytes
  let (totalFilled, bytes) ← decodeUIntLE 4 bytes
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (cancelReason, bytes) ← decodeUInt 1 bytes
  pure ({ timestamp, execId, clientOrderId, correlationId, orderId, receiveTime, totalFilled, instrumentId, cancelReason }, bytes)

@[simp] theorem encode_length (message : OrderCanceledMessage) : (encode message).length = 57 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : OrderCanceledMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderCanceledMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderCanceledMessage

/-- Cancel Order Reject Message: 64 bytes -/
structure CancelOrderRejectMessage where
  timestamp : BitVec 64
  clientOrderId : BitVec 64
  correlationId : BitVec 64
  orderIdOptional : BitVec 64
  cancelOrderRejectReason : BitVec 8
  cancelOrderRejectDetails : Alpha 31
  deriving DecidableEq, Repr

namespace CancelOrderRejectMessage

def encode (message : CancelOrderRejectMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.clientOrderId
    ++ (encodeUIntLE 8 message.correlationId
    ++ (encodeUIntLE 8 message.orderIdOptional
    ++ (encodeUInt 1 message.cancelOrderRejectReason
    ++ (Alpha.encode message.cancelOrderRejectDetails)))))

def decode (bytes : List UInt8) : Option (CancelOrderRejectMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (clientOrderId, bytes) ← decodeUIntLE 8 bytes
  let (correlationId, bytes) ← decodeUIntLE 8 bytes
  let (orderIdOptional, bytes) ← decodeUIntLE 8 bytes
  let (cancelOrderRejectReason, bytes) ← decodeUInt 1 bytes
  let (cancelOrderRejectDetails, bytes) ← Alpha.decode 31 bytes
  pure ({ timestamp, clientOrderId, correlationId, orderIdOptional, cancelOrderRejectReason, cancelOrderRejectDetails }, bytes)

@[simp] theorem encode_length (message : CancelOrderRejectMessage) : (encode message).length = 64 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : CancelOrderRejectMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CancelOrderRejectMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end CancelOrderRejectMessage

/-- Mass Cancel Order Message: 23 bytes -/
structure MassCancelOrderMessage where
  correlationId : BitVec 64
  limitPrice : BitVec 64
  instrumentId : BitVec 32
  side : BitVec 8
  currentSessionOnly : BitVec 8
  requestTradingLock : BitVec 8
  deriving DecidableEq, Repr

namespace MassCancelOrderMessage

def encode (message : MassCancelOrderMessage) : List UInt8 :=
  encodeUIntLE 8 message.correlationId
    ++ (encodeUIntLE 8 message.limitPrice
    ++ (encodeUIntLE 4 message.instrumentId
    ++ (encodeUInt 1 message.side
    ++ (encodeUInt 1 message.currentSessionOnly
    ++ (encodeUInt 1 message.requestTradingLock)))))

def decode (bytes : List UInt8) : Option (MassCancelOrderMessage × List UInt8) := do
  let (correlationId, bytes) ← decodeUIntLE 8 bytes
  let (limitPrice, bytes) ← decodeUIntLE 8 bytes
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (currentSessionOnly, bytes) ← decodeUInt 1 bytes
  let (requestTradingLock, bytes) ← decodeUInt 1 bytes
  pure ({ correlationId, limitPrice, instrumentId, side, currentSessionOnly, requestTradingLock }, bytes)

@[simp] theorem encode_length (message : MassCancelOrderMessage) : (encode message).length = 23 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : MassCancelOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MassCancelOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end MassCancelOrderMessage

/-- Mass Cancel Order Ack Message: 30 bytes -/
structure MassCancelOrderAckMessage where
  timestamp : BitVec 64
  execId : BitVec 64
  correlationId : BitVec 64
  canceledCount : BitVec 32
  onlyCurrentSession : BitVec 8
  tradingLockApplied : BitVec 8
  deriving DecidableEq, Repr

namespace MassCancelOrderAckMessage

def encode (message : MassCancelOrderAckMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.execId
    ++ (encodeUIntLE 8 message.correlationId
    ++ (encodeUIntLE 4 message.canceledCount
    ++ (encodeUInt 1 message.onlyCurrentSession
    ++ (encodeUInt 1 message.tradingLockApplied)))))

def decode (bytes : List UInt8) : Option (MassCancelOrderAckMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  let (correlationId, bytes) ← decodeUIntLE 8 bytes
  let (canceledCount, bytes) ← decodeUIntLE 4 bytes
  let (onlyCurrentSession, bytes) ← decodeUInt 1 bytes
  let (tradingLockApplied, bytes) ← decodeUInt 1 bytes
  pure ({ timestamp, execId, correlationId, canceledCount, onlyCurrentSession, tradingLockApplied }, bytes)

@[simp] theorem encode_length (message : MassCancelOrderAckMessage) : (encode message).length = 30 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : MassCancelOrderAckMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MassCancelOrderAckMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end MassCancelOrderAckMessage

/-- Mass Cancel Order Reject Message: 48 bytes -/
structure MassCancelOrderRejectMessage where
  timestamp : BitVec 64
  correlationId : BitVec 64
  errorMessage : Alpha 32
  deriving DecidableEq, Repr

namespace MassCancelOrderRejectMessage

def encode (message : MassCancelOrderRejectMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.correlationId
    ++ (Alpha.encode message.errorMessage))

def decode (bytes : List UInt8) : Option (MassCancelOrderRejectMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (correlationId, bytes) ← decodeUIntLE 8 bytes
  let (errorMessage, bytes) ← Alpha.decode 32 bytes
  pure ({ timestamp, correlationId, errorMessage }, bytes)

@[simp] theorem encode_length (message : MassCancelOrderRejectMessage) : (encode message).length = 48 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : MassCancelOrderRejectMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MassCancelOrderRejectMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end MassCancelOrderRejectMessage

/-- Unlock Trading Message: 9 bytes -/
structure UnlockTradingMessage where
  correlationId : BitVec 64
  currentSessionOnly : BitVec 8
  deriving DecidableEq, Repr

namespace UnlockTradingMessage

def encode (message : UnlockTradingMessage) : List UInt8 :=
  encodeUIntLE 8 message.correlationId
    ++ (encodeUInt 1 message.currentSessionOnly)

def decode (bytes : List UInt8) : Option (UnlockTradingMessage × List UInt8) := do
  let (correlationId, bytes) ← decodeUIntLE 8 bytes
  let (currentSessionOnly, bytes) ← decodeUInt 1 bytes
  pure ({ correlationId, currentSessionOnly }, bytes)

@[simp] theorem encode_length (message : UnlockTradingMessage) : (encode message).length = 9 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : UnlockTradingMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UnlockTradingMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end UnlockTradingMessage

/-- Unlock Trading Ack Message: 20 bytes -/
structure UnlockTradingAckMessage where
  timestamp : BitVec 64
  correlationId : BitVec 64
  numUsersAffected : BitVec 32
  deriving DecidableEq, Repr

namespace UnlockTradingAckMessage

def encode (message : UnlockTradingAckMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.correlationId
    ++ (encodeUIntLE 4 message.numUsersAffected))

def decode (bytes : List UInt8) : Option (UnlockTradingAckMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (correlationId, bytes) ← decodeUIntLE 8 bytes
  let (numUsersAffected, bytes) ← decodeUIntLE 4 bytes
  pure ({ timestamp, correlationId, numUsersAffected }, bytes)

@[simp] theorem encode_length (message : UnlockTradingAckMessage) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : UnlockTradingAckMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UnlockTradingAckMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end UnlockTradingAckMessage

/-- Unlock Trading Reject Message: 48 bytes -/
structure UnlockTradingRejectMessage where
  timestamp : BitVec 64
  correlationId : BitVec 64
  errorMessage : Alpha 32
  deriving DecidableEq, Repr

namespace UnlockTradingRejectMessage

def encode (message : UnlockTradingRejectMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.correlationId
    ++ (Alpha.encode message.errorMessage))

def decode (bytes : List UInt8) : Option (UnlockTradingRejectMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (correlationId, bytes) ← decodeUIntLE 8 bytes
  let (errorMessage, bytes) ← Alpha.decode 32 bytes
  pure ({ timestamp, correlationId, errorMessage }, bytes)

@[simp] theorem encode_length (message : UnlockTradingRejectMessage) : (encode message).length = 48 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : UnlockTradingRejectMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UnlockTradingRejectMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end UnlockTradingRejectMessage

/-- Order Filled Message: 81 bytes -/
structure OrderFilledMessage where
  timestamp : BitVec 64
  execId : BitVec 64
  matchId : BitVec 64
  clientOrderId : BitVec 64
  correlationId : BitVec 64
  orderId : BitVec 64
  filledVwap : BitVec 64
  totalFilled : BitVec 32
  availableQty : BitVec 32
  fillPrice : BitVec 64
  fillQty : BitVec 32
  instrumentId : BitVec 32
  isAggressor : BitVec 8
  deriving DecidableEq, Repr

namespace OrderFilledMessage

def encode (message : OrderFilledMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.execId
    ++ (encodeUIntLE 8 message.matchId
    ++ (encodeUIntLE 8 message.clientOrderId
    ++ (encodeUIntLE 8 message.correlationId
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.filledVwap
    ++ (encodeUIntLE 4 message.totalFilled
    ++ (encodeUIntLE 4 message.availableQty
    ++ (encodeUIntLE 8 message.fillPrice
    ++ (encodeUIntLE 4 message.fillQty
    ++ (encodeUIntLE 4 message.instrumentId
    ++ (encodeUInt 1 message.isAggressor))))))))))))

def decode (bytes : List UInt8) : Option (OrderFilledMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  let (matchId, bytes) ← decodeUIntLE 8 bytes
  let (clientOrderId, bytes) ← decodeUIntLE 8 bytes
  let (correlationId, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (filledVwap, bytes) ← decodeUIntLE 8 bytes
  let (totalFilled, bytes) ← decodeUIntLE 4 bytes
  let (availableQty, bytes) ← decodeUIntLE 4 bytes
  let (fillPrice, bytes) ← decodeUIntLE 8 bytes
  let (fillQty, bytes) ← decodeUIntLE 4 bytes
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (isAggressor, bytes) ← decodeUInt 1 bytes
  pure ({ timestamp, execId, matchId, clientOrderId, correlationId, orderId, filledVwap, totalFilled, availableQty, fillPrice, fillQty, instrumentId, isAggressor }, bytes)

@[simp] theorem encode_length (message : OrderFilledMessage) : (encode message).length = 81 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : OrderFilledMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderFilledMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderFilledMessage

/-- Spread Order Filled Message: 97 bytes -/
structure SpreadOrderFilledMessage where
  timestamp : BitVec 64
  execId : BitVec 64
  matchId : BitVec 64
  clientOrderId : BitVec 64
  correlationId : BitVec 64
  orderId : BitVec 64
  filledVwap : BitVec 64
  totalFilled : BitVec 32
  availableQty : BitVec 32
  fillPrice : BitVec 64
  leg1FillPrice : BitVec 64
  leg2FillPrice : BitVec 64
  fillQty : BitVec 32
  instrumentId : BitVec 32
  isAggressor : BitVec 8
  deriving DecidableEq, Repr

namespace SpreadOrderFilledMessage

def encode (message : SpreadOrderFilledMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.execId
    ++ (encodeUIntLE 8 message.matchId
    ++ (encodeUIntLE 8 message.clientOrderId
    ++ (encodeUIntLE 8 message.correlationId
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.filledVwap
    ++ (encodeUIntLE 4 message.totalFilled
    ++ (encodeUIntLE 4 message.availableQty
    ++ (encodeUIntLE 8 message.fillPrice
    ++ (encodeUIntLE 8 message.leg1FillPrice
    ++ (encodeUIntLE 8 message.leg2FillPrice
    ++ (encodeUIntLE 4 message.fillQty
    ++ (encodeUIntLE 4 message.instrumentId
    ++ (encodeUInt 1 message.isAggressor))))))))))))))

def decode (bytes : List UInt8) : Option (SpreadOrderFilledMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  let (matchId, bytes) ← decodeUIntLE 8 bytes
  let (clientOrderId, bytes) ← decodeUIntLE 8 bytes
  let (correlationId, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (filledVwap, bytes) ← decodeUIntLE 8 bytes
  let (totalFilled, bytes) ← decodeUIntLE 4 bytes
  let (availableQty, bytes) ← decodeUIntLE 4 bytes
  let (fillPrice, bytes) ← decodeUIntLE 8 bytes
  let (leg1FillPrice, bytes) ← decodeUIntLE 8 bytes
  let (leg2FillPrice, bytes) ← decodeUIntLE 8 bytes
  let (fillQty, bytes) ← decodeUIntLE 4 bytes
  let (instrumentId, bytes) ← decodeUIntLE 4 bytes
  let (isAggressor, bytes) ← decodeUInt 1 bytes
  pure ({ timestamp, execId, matchId, clientOrderId, correlationId, orderId, filledVwap, totalFilled, availableQty, fillPrice, leg1FillPrice, leg2FillPrice, fillQty, instrumentId, isAggressor }, bytes)

@[simp] theorem encode_length (message : SpreadOrderFilledMessage) : (encode message).length = 97 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : SpreadOrderFilledMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SpreadOrderFilledMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SpreadOrderFilledMessage

/-- Last Exec Id Request Message: 8 bytes -/
structure LastExecIdRequestMessage where
  correlationId : BitVec 64
  deriving DecidableEq, Repr

namespace LastExecIdRequestMessage

def encode (message : LastExecIdRequestMessage) : List UInt8 :=
  encodeUIntLE 8 message.correlationId

def decode (bytes : List UInt8) : Option (LastExecIdRequestMessage × List UInt8) := do
  let (correlationId, bytes) ← decodeUIntLE 8 bytes
  pure ({ correlationId }, bytes)

@[simp] theorem encode_length (message : LastExecIdRequestMessage) : (encode message).length = 8 := by
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : LastExecIdRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LastExecIdRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end LastExecIdRequestMessage

/-- Last Exec Id Message: 24 bytes -/
structure LastExecIdMessage where
  timestamp : BitVec 64
  lastExecId : BitVec 64
  correlationId : BitVec 64
  deriving DecidableEq, Repr

namespace LastExecIdMessage

def encode (message : LastExecIdMessage) : List UInt8 :=
  encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.lastExecId
    ++ (encodeUIntLE 8 message.correlationId))

def decode (bytes : List UInt8) : Option (LastExecIdMessage × List UInt8) := do
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (lastExecId, bytes) ← decodeUIntLE 8 bytes
  let (correlationId, bytes) ← decodeUIntLE 8 bytes
  pure ({ timestamp, lastExecId, correlationId }, bytes)

@[simp] theorem encode_length (message : LastExecIdMessage) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : LastExecIdMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LastExecIdMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end LastExecIdMessage

/-- Event Resend Request Message: 24 bytes -/
structure EventResendRequestMessage where
  correlationId : BitVec 64
  beginExecId : BitVec 64
  endExecId : BitVec 64
  deriving DecidableEq, Repr

namespace EventResendRequestMessage

def encode (message : EventResendRequestMessage) : List UInt8 :=
  encodeUIntLE 8 message.correlationId
    ++ (encodeUIntLE 8 message.beginExecId
    ++ (encodeUIntLE 8 message.endExecId))

def decode (bytes : List UInt8) : Option (EventResendRequestMessage × List UInt8) := do
  let (correlationId, bytes) ← decodeUIntLE 8 bytes
  let (beginExecId, bytes) ← decodeUIntLE 8 bytes
  let (endExecId, bytes) ← decodeUIntLE 8 bytes
  pure ({ correlationId, beginExecId, endExecId }, bytes)

@[simp] theorem encode_length (message : EventResendRequestMessage) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : EventResendRequestMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EventResendRequestMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end EventResendRequestMessage

/-- Event Resend Complete Message: 12 bytes -/
structure EventResendCompleteMessage where
  correlationId : BitVec 64
  resentEventCount : BitVec 32
  deriving DecidableEq, Repr

namespace EventResendCompleteMessage

def encode (message : EventResendCompleteMessage) : List UInt8 :=
  encodeUIntLE 8 message.correlationId
    ++ (encodeUIntLE 4 message.resentEventCount)

def decode (bytes : List UInt8) : Option (EventResendCompleteMessage × List UInt8) := do
  let (correlationId, bytes) ← decodeUIntLE 8 bytes
  let (resentEventCount, bytes) ← decodeUIntLE 4 bytes
  pure ({ correlationId, resentEventCount }, bytes)

@[simp] theorem encode_length (message : EventResendCompleteMessage) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : EventResendCompleteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EventResendCompleteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end EventResendCompleteMessage

/-- Event Resend Reject Message: 64 bytes -/
structure EventResendRejectMessage where
  correlationId : BitVec 64
  resendRejectReason : BitVec 8
  detailsString55 : Alpha 55
  deriving DecidableEq, Repr

namespace EventResendRejectMessage

def encode (message : EventResendRejectMessage) : List UInt8 :=
  encodeUIntLE 8 message.correlationId
    ++ (encodeUInt 1 message.resendRejectReason
    ++ (Alpha.encode message.detailsString55))

def decode (bytes : List UInt8) : Option (EventResendRejectMessage × List UInt8) := do
  let (correlationId, bytes) ← decodeUIntLE 8 bytes
  let (resendRejectReason, bytes) ← decodeUInt 1 bytes
  let (detailsString55, bytes) ← Alpha.decode 55 bytes
  pure ({ correlationId, resendRejectReason, detailsString55 }, bytes)

@[simp] theorem encode_length (message : EventResendRejectMessage) : (encode message).length = 64 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : EventResendRejectMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EventResendRejectMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end EventResendRejectMessage

/-- Any Payload, selected by Schema Id and Template Id -/
inductive Payload where
  | logonMessage (message : LogonMessage) -- 1100, 100
  | logonConfMessage (message : LogonConfMessage) -- 1100, 200
  | logoutMessage (message : LogoutMessage) -- 1100, 101
  | loggedOutMessage (message : LoggedOutMessage) -- 1100, 201
  | heartbeatMessage (message : HeartbeatMessage) -- 1100, 10
  | testRequestMessage (message : TestRequestMessage) -- 1100, 11
  | resendRequestMessage (message : ResendRequestMessage) -- 1100, 102
  | gapFillMessage (message : GapFillMessage) -- 1100, 202
  | pingMessage (message : PingMessage) -- 1101, 102
  | pongMessage (message : PongMessage) -- 1101, 202
  | instrumentInfoRequestMessage (message : InstrumentInfoRequestMessage) -- 1101, 103
  | instrumentInfoMessage (message : InstrumentInfoMessage) -- 1101, 203
  | setAccountMessage (message : SetAccountMessage) -- 1101, 105
  | setTraderMessage (message : SetTraderMessage) -- 1101, 106
  | setAckMessage (message : SetAckMessage) -- 1101, 205
  | newOrderMessage (message : NewOrderMessage) -- 1101, 110
  | newIocOrderMessage (message : NewIocOrderMessage) -- 1101, 111
  | orderEnteredMessage (message : OrderEnteredMessage) -- 1101, 210
  | replaceOrderMessage (message : ReplaceOrderMessage) -- 1101, 120
  | obsoleteStreamOrderMessage (message : ObsoleteStreamOrderMessage) -- 1101, 121
  | orderRejectMessage (message : OrderRejectMessage) -- 1101, 221
  | orderReplacedMessage (message : OrderReplacedMessage) -- 1101, 220
  | cancelOrderMessage (message : CancelOrderMessage) -- 1101, 130
  | orderCanceledMessage (message : OrderCanceledMessage) -- 1101, 230
  | cancelOrderRejectMessage (message : CancelOrderRejectMessage) -- 1101, 233
  | massCancelOrderMessage (message : MassCancelOrderMessage) -- 1101, 131
  | massCancelOrderAckMessage (message : MassCancelOrderAckMessage) -- 1101, 231
  | massCancelOrderRejectMessage (message : MassCancelOrderRejectMessage) -- 1101, 232
  | unlockTradingMessage (message : UnlockTradingMessage) -- 1101, 132
  | unlockTradingAckMessage (message : UnlockTradingAckMessage) -- 1101, 234
  | unlockTradingRejectMessage (message : UnlockTradingRejectMessage) -- 1101, 235
  | orderFilledMessage (message : OrderFilledMessage) -- 1101, 240
  | spreadOrderFilledMessage (message : SpreadOrderFilledMessage) -- 1101, 241
  | lastExecIdRequestMessage (message : LastExecIdRequestMessage) -- 1101, 150
  | lastExecIdMessage (message : LastExecIdMessage) -- 1101, 250
  | eventResendRequestMessage (message : EventResendRequestMessage) -- 1101, 152
  | eventResendCompleteMessage (message : EventResendCompleteMessage) -- 1101, 252
  | eventResendRejectMessage (message : EventResendRejectMessage) -- 1101, 253
  deriving DecidableEq, Repr

namespace Payload

/-- The Schema Id each message is sent under -/
def schemaId : Payload → BitVec 16
  | .logonMessage _ => 1100
  | .logonConfMessage _ => 1100
  | .logoutMessage _ => 1100
  | .loggedOutMessage _ => 1100
  | .heartbeatMessage _ => 1100
  | .testRequestMessage _ => 1100
  | .resendRequestMessage _ => 1100
  | .gapFillMessage _ => 1100
  | .pingMessage _ => 1101
  | .pongMessage _ => 1101
  | .instrumentInfoRequestMessage _ => 1101
  | .instrumentInfoMessage _ => 1101
  | .setAccountMessage _ => 1101
  | .setTraderMessage _ => 1101
  | .setAckMessage _ => 1101
  | .newOrderMessage _ => 1101
  | .newIocOrderMessage _ => 1101
  | .orderEnteredMessage _ => 1101
  | .replaceOrderMessage _ => 1101
  | .obsoleteStreamOrderMessage _ => 1101
  | .orderRejectMessage _ => 1101
  | .orderReplacedMessage _ => 1101
  | .cancelOrderMessage _ => 1101
  | .orderCanceledMessage _ => 1101
  | .cancelOrderRejectMessage _ => 1101
  | .massCancelOrderMessage _ => 1101
  | .massCancelOrderAckMessage _ => 1101
  | .massCancelOrderRejectMessage _ => 1101
  | .unlockTradingMessage _ => 1101
  | .unlockTradingAckMessage _ => 1101
  | .unlockTradingRejectMessage _ => 1101
  | .orderFilledMessage _ => 1101
  | .spreadOrderFilledMessage _ => 1101
  | .lastExecIdRequestMessage _ => 1101
  | .lastExecIdMessage _ => 1101
  | .eventResendRequestMessage _ => 1101
  | .eventResendCompleteMessage _ => 1101
  | .eventResendRejectMessage _ => 1101

/-- The Template Id each message is sent under -/
def templateId : Payload → BitVec 16
  | .logonMessage _ => 100
  | .logonConfMessage _ => 200
  | .logoutMessage _ => 101
  | .loggedOutMessage _ => 201
  | .heartbeatMessage _ => 10
  | .testRequestMessage _ => 11
  | .resendRequestMessage _ => 102
  | .gapFillMessage _ => 202
  | .pingMessage _ => 102
  | .pongMessage _ => 202
  | .instrumentInfoRequestMessage _ => 103
  | .instrumentInfoMessage _ => 203
  | .setAccountMessage _ => 105
  | .setTraderMessage _ => 106
  | .setAckMessage _ => 205
  | .newOrderMessage _ => 110
  | .newIocOrderMessage _ => 111
  | .orderEnteredMessage _ => 210
  | .replaceOrderMessage _ => 120
  | .obsoleteStreamOrderMessage _ => 121
  | .orderRejectMessage _ => 221
  | .orderReplacedMessage _ => 220
  | .cancelOrderMessage _ => 130
  | .orderCanceledMessage _ => 230
  | .cancelOrderRejectMessage _ => 233
  | .massCancelOrderMessage _ => 131
  | .massCancelOrderAckMessage _ => 231
  | .massCancelOrderRejectMessage _ => 232
  | .unlockTradingMessage _ => 132
  | .unlockTradingAckMessage _ => 234
  | .unlockTradingRejectMessage _ => 235
  | .orderFilledMessage _ => 240
  | .spreadOrderFilledMessage _ => 241
  | .lastExecIdRequestMessage _ => 150
  | .lastExecIdMessage _ => 250
  | .eventResendRequestMessage _ => 152
  | .eventResendCompleteMessage _ => 252
  | .eventResendRejectMessage _ => 253

def encode : Payload → List UInt8
  | .logonMessage message => LogonMessage.encode message
  | .logonConfMessage message => LogonConfMessage.encode message
  | .logoutMessage message => LogoutMessage.encode message
  | .loggedOutMessage message => LoggedOutMessage.encode message
  | .heartbeatMessage message => HeartbeatMessage.encode message
  | .testRequestMessage message => TestRequestMessage.encode message
  | .resendRequestMessage message => ResendRequestMessage.encode message
  | .gapFillMessage message => GapFillMessage.encode message
  | .pingMessage message => PingMessage.encode message
  | .pongMessage message => PongMessage.encode message
  | .instrumentInfoRequestMessage message => InstrumentInfoRequestMessage.encode message
  | .instrumentInfoMessage message => InstrumentInfoMessage.encode message
  | .setAccountMessage message => SetAccountMessage.encode message
  | .setTraderMessage message => SetTraderMessage.encode message
  | .setAckMessage message => SetAckMessage.encode message
  | .newOrderMessage message => NewOrderMessage.encode message
  | .newIocOrderMessage message => NewIocOrderMessage.encode message
  | .orderEnteredMessage message => OrderEnteredMessage.encode message
  | .replaceOrderMessage message => ReplaceOrderMessage.encode message
  | .obsoleteStreamOrderMessage message => ObsoleteStreamOrderMessage.encode message
  | .orderRejectMessage message => OrderRejectMessage.encode message
  | .orderReplacedMessage message => OrderReplacedMessage.encode message
  | .cancelOrderMessage message => CancelOrderMessage.encode message
  | .orderCanceledMessage message => OrderCanceledMessage.encode message
  | .cancelOrderRejectMessage message => CancelOrderRejectMessage.encode message
  | .massCancelOrderMessage message => MassCancelOrderMessage.encode message
  | .massCancelOrderAckMessage message => MassCancelOrderAckMessage.encode message
  | .massCancelOrderRejectMessage message => MassCancelOrderRejectMessage.encode message
  | .unlockTradingMessage message => UnlockTradingMessage.encode message
  | .unlockTradingAckMessage message => UnlockTradingAckMessage.encode message
  | .unlockTradingRejectMessage message => UnlockTradingRejectMessage.encode message
  | .orderFilledMessage message => OrderFilledMessage.encode message
  | .spreadOrderFilledMessage message => SpreadOrderFilledMessage.encode message
  | .lastExecIdRequestMessage message => LastExecIdRequestMessage.encode message
  | .lastExecIdMessage message => LastExecIdMessage.encode message
  | .eventResendRequestMessage message => EventResendRequestMessage.encode message
  | .eventResendCompleteMessage message => EventResendCompleteMessage.encode message
  | .eventResendRejectMessage message => EventResendRejectMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 281 := by
  cases message with
  | logonMessage inner =>
    simp only [encode, LogonMessage.encode_length]
    omega
  | logonConfMessage inner =>
    simp only [encode, LogonConfMessage.encode_length]
    omega
  | logoutMessage inner =>
    simp only [encode, LogoutMessage.encode_length]
    omega
  | loggedOutMessage inner =>
    simp only [encode, LoggedOutMessage.encode_length]
    omega
  | heartbeatMessage inner =>
    simp only [encode, HeartbeatMessage.encode_length]
    omega
  | testRequestMessage inner =>
    simp only [encode, TestRequestMessage.encode_length]
    omega
  | resendRequestMessage inner =>
    simp only [encode, ResendRequestMessage.encode_length]
    omega
  | gapFillMessage inner =>
    simp only [encode, GapFillMessage.encode_length]
    omega
  | pingMessage inner =>
    have bound_inner := PingMessage.encode_length_le inner
    simp only [encode]
    omega
  | pongMessage inner =>
    have bound_inner := PongMessage.encode_length_le inner
    simp only [encode]
    omega
  | instrumentInfoRequestMessage inner =>
    simp only [encode, InstrumentInfoRequestMessage.encode_length]
    omega
  | instrumentInfoMessage inner =>
    simp only [encode, InstrumentInfoMessage.encode_length]
    omega
  | setAccountMessage inner =>
    simp only [encode, SetAccountMessage.encode_length]
    omega
  | setTraderMessage inner =>
    simp only [encode, SetTraderMessage.encode_length]
    omega
  | setAckMessage inner =>
    simp only [encode, SetAckMessage.encode_length]
    omega
  | newOrderMessage inner =>
    simp only [encode, NewOrderMessage.encode_length]
    omega
  | newIocOrderMessage inner =>
    simp only [encode, NewIocOrderMessage.encode_length]
    omega
  | orderEnteredMessage inner =>
    simp only [encode, OrderEnteredMessage.encode_length]
    omega
  | replaceOrderMessage inner =>
    simp only [encode, ReplaceOrderMessage.encode_length]
    omega
  | obsoleteStreamOrderMessage inner =>
    simp only [encode, ObsoleteStreamOrderMessage.encode_length]
    omega
  | orderRejectMessage inner =>
    simp only [encode, OrderRejectMessage.encode_length]
    omega
  | orderReplacedMessage inner =>
    simp only [encode, OrderReplacedMessage.encode_length]
    omega
  | cancelOrderMessage inner =>
    simp only [encode, CancelOrderMessage.encode_length]
    omega
  | orderCanceledMessage inner =>
    simp only [encode, OrderCanceledMessage.encode_length]
    omega
  | cancelOrderRejectMessage inner =>
    simp only [encode, CancelOrderRejectMessage.encode_length]
    omega
  | massCancelOrderMessage inner =>
    simp only [encode, MassCancelOrderMessage.encode_length]
    omega
  | massCancelOrderAckMessage inner =>
    simp only [encode, MassCancelOrderAckMessage.encode_length]
    omega
  | massCancelOrderRejectMessage inner =>
    simp only [encode, MassCancelOrderRejectMessage.encode_length]
    omega
  | unlockTradingMessage inner =>
    simp only [encode, UnlockTradingMessage.encode_length]
    omega
  | unlockTradingAckMessage inner =>
    simp only [encode, UnlockTradingAckMessage.encode_length]
    omega
  | unlockTradingRejectMessage inner =>
    simp only [encode, UnlockTradingRejectMessage.encode_length]
    omega
  | orderFilledMessage inner =>
    simp only [encode, OrderFilledMessage.encode_length]
    omega
  | spreadOrderFilledMessage inner =>
    simp only [encode, SpreadOrderFilledMessage.encode_length]
    omega
  | lastExecIdRequestMessage inner =>
    simp only [encode, LastExecIdRequestMessage.encode_length]
    omega
  | lastExecIdMessage inner =>
    simp only [encode, LastExecIdMessage.encode_length]
    omega
  | eventResendRequestMessage inner =>
    simp only [encode, EventResendRequestMessage.encode_length]
    omega
  | eventResendCompleteMessage inner =>
    simp only [encode, EventResendCompleteMessage.encode_length]
    omega
  | eventResendRejectMessage inner =>
    simp only [encode, EventResendRejectMessage.encode_length]
    omega

def decode (schemaId : BitVec 16) (templateId : BitVec 16) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if schemaId = 1100 ∧ templateId = 100 then (LogonMessage.decode bytes).map fun (message, rest) => (.logonMessage message, rest)
  else if schemaId = 1100 ∧ templateId = 200 then (LogonConfMessage.decode bytes).map fun (message, rest) => (.logonConfMessage message, rest)
  else if schemaId = 1100 ∧ templateId = 101 then (LogoutMessage.decode bytes).map fun (message, rest) => (.logoutMessage message, rest)
  else if schemaId = 1100 ∧ templateId = 201 then (LoggedOutMessage.decode bytes).map fun (message, rest) => (.loggedOutMessage message, rest)
  else if schemaId = 1100 ∧ templateId = 10 then (HeartbeatMessage.decode bytes).map fun (message, rest) => (.heartbeatMessage message, rest)
  else if schemaId = 1100 ∧ templateId = 11 then (TestRequestMessage.decode bytes).map fun (message, rest) => (.testRequestMessage message, rest)
  else if schemaId = 1100 ∧ templateId = 102 then (ResendRequestMessage.decode bytes).map fun (message, rest) => (.resendRequestMessage message, rest)
  else if schemaId = 1100 ∧ templateId = 202 then (GapFillMessage.decode bytes).map fun (message, rest) => (.gapFillMessage message, rest)
  else if schemaId = 1101 ∧ templateId = 102 then (PingMessage.decode bytes).map fun (message, rest) => (.pingMessage message, rest)
  else if schemaId = 1101 ∧ templateId = 202 then (PongMessage.decode bytes).map fun (message, rest) => (.pongMessage message, rest)
  else if schemaId = 1101 ∧ templateId = 103 then (InstrumentInfoRequestMessage.decode bytes).map fun (message, rest) => (.instrumentInfoRequestMessage message, rest)
  else if schemaId = 1101 ∧ templateId = 203 then (InstrumentInfoMessage.decode bytes).map fun (message, rest) => (.instrumentInfoMessage message, rest)
  else if schemaId = 1101 ∧ templateId = 105 then (SetAccountMessage.decode bytes).map fun (message, rest) => (.setAccountMessage message, rest)
  else if schemaId = 1101 ∧ templateId = 106 then (SetTraderMessage.decode bytes).map fun (message, rest) => (.setTraderMessage message, rest)
  else if schemaId = 1101 ∧ templateId = 205 then (SetAckMessage.decode bytes).map fun (message, rest) => (.setAckMessage message, rest)
  else if schemaId = 1101 ∧ templateId = 110 then (NewOrderMessage.decode bytes).map fun (message, rest) => (.newOrderMessage message, rest)
  else if schemaId = 1101 ∧ templateId = 111 then (NewIocOrderMessage.decode bytes).map fun (message, rest) => (.newIocOrderMessage message, rest)
  else if schemaId = 1101 ∧ templateId = 210 then (OrderEnteredMessage.decode bytes).map fun (message, rest) => (.orderEnteredMessage message, rest)
  else if schemaId = 1101 ∧ templateId = 120 then (ReplaceOrderMessage.decode bytes).map fun (message, rest) => (.replaceOrderMessage message, rest)
  else if schemaId = 1101 ∧ templateId = 121 then (ObsoleteStreamOrderMessage.decode bytes).map fun (message, rest) => (.obsoleteStreamOrderMessage message, rest)
  else if schemaId = 1101 ∧ templateId = 221 then (OrderRejectMessage.decode bytes).map fun (message, rest) => (.orderRejectMessage message, rest)
  else if schemaId = 1101 ∧ templateId = 220 then (OrderReplacedMessage.decode bytes).map fun (message, rest) => (.orderReplacedMessage message, rest)
  else if schemaId = 1101 ∧ templateId = 130 then (CancelOrderMessage.decode bytes).map fun (message, rest) => (.cancelOrderMessage message, rest)
  else if schemaId = 1101 ∧ templateId = 230 then (OrderCanceledMessage.decode bytes).map fun (message, rest) => (.orderCanceledMessage message, rest)
  else if schemaId = 1101 ∧ templateId = 233 then (CancelOrderRejectMessage.decode bytes).map fun (message, rest) => (.cancelOrderRejectMessage message, rest)
  else if schemaId = 1101 ∧ templateId = 131 then (MassCancelOrderMessage.decode bytes).map fun (message, rest) => (.massCancelOrderMessage message, rest)
  else if schemaId = 1101 ∧ templateId = 231 then (MassCancelOrderAckMessage.decode bytes).map fun (message, rest) => (.massCancelOrderAckMessage message, rest)
  else if schemaId = 1101 ∧ templateId = 232 then (MassCancelOrderRejectMessage.decode bytes).map fun (message, rest) => (.massCancelOrderRejectMessage message, rest)
  else if schemaId = 1101 ∧ templateId = 132 then (UnlockTradingMessage.decode bytes).map fun (message, rest) => (.unlockTradingMessage message, rest)
  else if schemaId = 1101 ∧ templateId = 234 then (UnlockTradingAckMessage.decode bytes).map fun (message, rest) => (.unlockTradingAckMessage message, rest)
  else if schemaId = 1101 ∧ templateId = 235 then (UnlockTradingRejectMessage.decode bytes).map fun (message, rest) => (.unlockTradingRejectMessage message, rest)
  else if schemaId = 1101 ∧ templateId = 240 then (OrderFilledMessage.decode bytes).map fun (message, rest) => (.orderFilledMessage message, rest)
  else if schemaId = 1101 ∧ templateId = 241 then (SpreadOrderFilledMessage.decode bytes).map fun (message, rest) => (.spreadOrderFilledMessage message, rest)
  else if schemaId = 1101 ∧ templateId = 150 then (LastExecIdRequestMessage.decode bytes).map fun (message, rest) => (.lastExecIdRequestMessage message, rest)
  else if schemaId = 1101 ∧ templateId = 250 then (LastExecIdMessage.decode bytes).map fun (message, rest) => (.lastExecIdMessage message, rest)
  else if schemaId = 1101 ∧ templateId = 152 then (EventResendRequestMessage.decode bytes).map fun (message, rest) => (.eventResendRequestMessage message, rest)
  else if schemaId = 1101 ∧ templateId = 252 then (EventResendCompleteMessage.decode bytes).map fun (message, rest) => (.eventResendCompleteMessage message, rest)
  else if schemaId = 1101 ∧ templateId = 253 then (EventResendRejectMessage.decode bytes).map fun (message, rest) => (.eventResendRejectMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (schemaId message) (templateId message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, schemaId, templateId]

end Payload

/-- Sbe Message -/
structure SbeMessage where
  protocolId : BitVec 8
  flags : BitVec 8
  sequenceNumber : BitVec 32
  lastProcessedSeqNo : BitVec 32
  reserved : BitVec 32
  sendTimeEpochNanos : BitVec 64
  blockLength : BitVec 16
  version : BitVec 16
  payload : Payload
  padding : Capped 65222
  deriving DecidableEq, Repr

namespace SbeMessage

def encodeBody (message : SbeMessage) : List UInt8 :=
  encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 4 message.lastProcessedSeqNo
    ++ (encodeUIntLE 4 message.reserved
    ++ (encodeUIntLE 8 message.sendTimeEpochNanos
    ++ (encodeUIntLE 2 message.blockLength
    ++ (encodeUIntLE 2 (Payload.templateId message.payload)
    ++ (encodeUIntLE 2 (Payload.schemaId message.payload)
    ++ (encodeUIntLE 2 message.version
    ++ (Payload.encode message.payload
    ++ (message.padding.val)))))))))

def decodeBody (protocolId : BitVec 8) (flags : BitVec 8) (bytes : List UInt8) : Option SbeMessage := do
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (lastProcessedSeqNo, bytes) ← decodeUIntLE 4 bytes
  let (reserved, bytes) ← decodeUIntLE 4 bytes
  let (sendTimeEpochNanos, bytes) ← decodeUIntLE 8 bytes
  let (blockLength, bytes) ← decodeUIntLE 2 bytes
  let (templateId, bytes) ← decodeUIntLE 2 bytes
  let (schemaId, bytes) ← decodeUIntLE 2 bytes
  let (version, bytes) ← decodeUIntLE 2 bytes
  let (payload, bytes) ← Payload.decode schemaId templateId bytes
  let padding_ := bytes
  if fits_padding : padding_.length ≤ 65222 then
    pure { protocolId, flags, sequenceNumber, lastProcessedSeqNo, reserved, sendTimeEpochNanos, blockLength, version, payload, padding := ⟨padding_, fits_padding⟩ }
  else none

theorem decodeBody_encodeBody (message : SbeMessage) : decodeBody message.protocolId message.flags (encodeBody message) = some message := by
  unfold decodeBody encodeBody
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Payload.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.padding.length_le]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : SbeMessage) : (encodeBody message).length + 4 < 256 ^ 2 := by
  have bound_padding := message.padding.length_le
  unfold encodeBody
  cases message.payload with
  | logonMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, LogonMessage.encode_length]
    omega
  | logonConfMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, LogonConfMessage.encode_length]
    omega
  | logoutMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, LogoutMessage.encode_length]
    omega
  | loggedOutMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, LoggedOutMessage.encode_length]
    omega
  | heartbeatMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, HeartbeatMessage.encode_length]
    omega
  | testRequestMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, TestRequestMessage.encode_length]
    omega
  | resendRequestMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, ResendRequestMessage.encode_length]
    omega
  | gapFillMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, GapFillMessage.encode_length]
    omega
  | pingMessage inner =>
    have bound_inner := PingMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | pongMessage inner =>
    have bound_inner := PongMessage.encode_length_le inner
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length]
    omega
  | instrumentInfoRequestMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, InstrumentInfoRequestMessage.encode_length]
    omega
  | instrumentInfoMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, InstrumentInfoMessage.encode_length]
    omega
  | setAccountMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, SetAccountMessage.encode_length]
    omega
  | setTraderMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, SetTraderMessage.encode_length]
    omega
  | setAckMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, SetAckMessage.encode_length]
    omega
  | newOrderMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, NewOrderMessage.encode_length]
    omega
  | newIocOrderMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, NewIocOrderMessage.encode_length]
    omega
  | orderEnteredMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, OrderEnteredMessage.encode_length]
    omega
  | replaceOrderMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, ReplaceOrderMessage.encode_length]
    omega
  | obsoleteStreamOrderMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, ObsoleteStreamOrderMessage.encode_length]
    omega
  | orderRejectMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, OrderRejectMessage.encode_length]
    omega
  | orderReplacedMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, OrderReplacedMessage.encode_length]
    omega
  | cancelOrderMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, CancelOrderMessage.encode_length]
    omega
  | orderCanceledMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, OrderCanceledMessage.encode_length]
    omega
  | cancelOrderRejectMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, CancelOrderRejectMessage.encode_length]
    omega
  | massCancelOrderMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, MassCancelOrderMessage.encode_length]
    omega
  | massCancelOrderAckMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, MassCancelOrderAckMessage.encode_length]
    omega
  | massCancelOrderRejectMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, MassCancelOrderRejectMessage.encode_length]
    omega
  | unlockTradingMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, UnlockTradingMessage.encode_length]
    omega
  | unlockTradingAckMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, UnlockTradingAckMessage.encode_length]
    omega
  | unlockTradingRejectMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, UnlockTradingRejectMessage.encode_length]
    omega
  | orderFilledMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, OrderFilledMessage.encode_length]
    omega
  | spreadOrderFilledMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, SpreadOrderFilledMessage.encode_length]
    omega
  | lastExecIdRequestMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, LastExecIdRequestMessage.encode_length]
    omega
  | lastExecIdMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, LastExecIdMessage.encode_length]
    omega
  | eventResendRequestMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, EventResendRequestMessage.encode_length]
    omega
  | eventResendCompleteMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, EventResendCompleteMessage.encode_length]
    omega
  | eventResendRejectMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, EventResendRejectMessage.encode_length]
    omega

/-- Size rule: Message Length counts the bytes after it plus 4, so it is written from the body and checked on decode; Protocol Id, Flags are read ahead of it -/
def encode (message : SbeMessage) : List UInt8 :=
  encodeUInt 1 message.protocolId
    ++ (encodeUIntLE 1 message.flags
    ++ (encodeFramedLE 2 4 encodeBody message))

def decode (bytes : List UInt8) : Option (SbeMessage × List UInt8) := do
  let (protocolId, bytes) ← decodeUInt 1 bytes
  let (flags, bytes) ← decodeUIntLE 1 bytes
  decodeFramedAllLE 2 4 (decodeBody protocolId flags) bytes

@[simp] theorem decode_encode (message : SbeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  exact decodeFramedAllLE_encodeFramedLE 2 4 encodeBody (decodeBody message.protocolId message.flags) message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : SbeMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, encodeUIntLE_length, List.length_append, ← Nat.add_assoc, encodeFramedLE_length]
  omega

end SbeMessage

/-- Packet -/
structure Packet where
  sbeMessage : List SbeMessage
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeMany SbeMessage.encode message.sbeMessage

def decode (bytes : List UInt8) : Option Packet := do
  let sbeMessage ← decodeAll SbeMessage.decode bytes.length bytes
  pure { sbeMessage }

theorem decode_encode (message : Packet) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeAll_encodeMany SbeMessage.encode SbeMessage.decode SbeMessage.decode_encode SbeMessage.encode_length_pos message.sbeMessage _ (encodeMany_length_ge SbeMessage.encode SbeMessage.encode_length_pos message.sbeMessage), some_bind]
  rfl

end Packet

end Omi.CoinbaseCoinbasederivativesOrdersapiSbeV16
