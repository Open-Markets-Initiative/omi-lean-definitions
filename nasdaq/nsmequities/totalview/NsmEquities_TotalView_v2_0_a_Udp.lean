import Wire

/-!
# National Association of Securities Dealers Automated Quotations (Nasdaq) TotalView Itch v2.0.a

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.NasdaqNsmequitiesTotalviewAsciiitchV20AUdp

/-- Event Code: one byte code -/
def EventCode.codes : List UInt8 :=
  [0x53, 0x45]

inductive EventCode where
  | startOfDay -- Start Of Day
  | endOfDay -- End Of Day
  | unlisted (byte : { byte : UInt8 // byte ∉ EventCode.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace EventCode

def toByte : EventCode → UInt8
  | .startOfDay => 0x53
  | .endOfDay => 0x45
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : EventCode :=
  if byte = 0x53 then .startOfDay
  else .endOfDay

def ofByte (byte : UInt8) : EventCode :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : EventCode) : ofByte value.toByte = value := by
  cases value with
  | startOfDay => decide
  | endOfDay => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : EventCode) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (EventCode × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : EventCode) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : EventCode) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : EventCode) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end EventCode

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

theorem encode_length_pos (value : Side) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Side) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Side

/-- Display: one byte code -/
def Display.codes : List UInt8 :=
  [0x59, 0x41]

inductive Display where
  | displayed -- Displayed
  | attributable -- Attributable
  | unlisted (byte : { byte : UInt8 // byte ∉ Display.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Display

def toByte : Display → UInt8
  | .displayed => 0x59
  | .attributable => 0x41
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Display :=
  if byte = 0x59 then .displayed
  else .attributable

def ofByte (byte : UInt8) : Display :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Display) : ofByte value.toByte = value := by
  cases value with
  | displayed => decide
  | attributable => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Display) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Display × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Display) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : Display) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : Display) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Display

/-- Stock Halted: one byte code -/
def StockHalted.codes : List UInt8 :=
  [0x54, 0x46]

inductive StockHalted where
  | halted -- Halted
  | trading -- Trading
  | unlisted (byte : { byte : UInt8 // byte ∉ StockHalted.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace StockHalted

def toByte : StockHalted → UInt8
  | .halted => 0x54
  | .trading => 0x46
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : StockHalted :=
  if byte = 0x54 then .halted
  else .trading

def ofByte (byte : UInt8) : StockHalted :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : StockHalted) : ofByte value.toByte = value := by
  cases value with
  | halted => decide
  | trading => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : StockHalted) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (StockHalted × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : StockHalted) : (encode value).length = 1 :=
  rfl

theorem encode_length_pos (value : StockHalted) : (encode value).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (value : StockHalted) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end StockHalted

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

/-- System Event Message: 1 bytes -/
structure SystemEventMessage where
  eventCode : EventCode
  deriving DecidableEq, Repr

namespace SystemEventMessage

def encode (message : SystemEventMessage) : List UInt8 :=
  EventCode.encode message.eventCode

def decode (bytes : List UInt8) : Option (SystemEventMessage × List UInt8) := do
  let (eventCode, bytes) ← EventCode.decode bytes
  pure ({ eventCode }, bytes)

@[simp] theorem encode_length (message : SystemEventMessage) : (encode message).length = 1 := by
  unfold encode
  simp only [EventCode.encode_length]

theorem encode_length_pos (message : SystemEventMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SystemEventMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [EventCode.decode_encode, some_bind]
  rfl

end SystemEventMessage

/-- Add Order Message: 37 bytes -/
structure AddOrderMessage where
  orderReferenceNumber : Alpha 9
  side : Side
  shares : Alpha 6
  stock : Alpha 6
  price : Alpha 10
  display : Display
  mmid : Alpha 4
  deriving DecidableEq, Repr

namespace AddOrderMessage

def encode (message : AddOrderMessage) : List UInt8 :=
  Alpha.encode message.orderReferenceNumber
    ++ (Side.encode message.side
    ++ (Alpha.encode message.shares
    ++ (Alpha.encode message.stock
    ++ (Alpha.encode message.price
    ++ (Display.encode message.display
    ++ (Alpha.encode message.mmid))))))

def decode (bytes : List UInt8) : Option (AddOrderMessage × List UInt8) := do
  let (orderReferenceNumber, bytes) ← Alpha.decode 9 bytes
  let (side, bytes) ← Side.decode bytes
  let (shares, bytes) ← Alpha.decode 6 bytes
  let (stock, bytes) ← Alpha.decode 6 bytes
  let (price, bytes) ← Alpha.decode 10 bytes
  let (display, bytes) ← Display.decode bytes
  let (mmid, bytes) ← Alpha.decode 4 bytes
  pure ({ orderReferenceNumber, side, shares, stock, price, display, mmid }, bytes)

@[simp] theorem encode_length (message : AddOrderMessage) : (encode message).length = 37 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, Side.encode_length, Display.encode_length]

theorem encode_length_pos (message : AddOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AddOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Display.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end AddOrderMessage

/-- Order Executed Message: 24 bytes -/
structure OrderExecutedMessage where
  orderReferenceNumber : Alpha 9
  executedShares : Alpha 6
  matchNumber : Alpha 9
  deriving DecidableEq, Repr

namespace OrderExecutedMessage

def encode (message : OrderExecutedMessage) : List UInt8 :=
  Alpha.encode message.orderReferenceNumber
    ++ (Alpha.encode message.executedShares
    ++ (Alpha.encode message.matchNumber))

def decode (bytes : List UInt8) : Option (OrderExecutedMessage × List UInt8) := do
  let (orderReferenceNumber, bytes) ← Alpha.decode 9 bytes
  let (executedShares, bytes) ← Alpha.decode 6 bytes
  let (matchNumber, bytes) ← Alpha.decode 9 bytes
  pure ({ orderReferenceNumber, executedShares, matchNumber }, bytes)

@[simp] theorem encode_length (message : OrderExecutedMessage) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : OrderExecutedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderExecutedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderExecutedMessage

/-- Order Cancel Message: 15 bytes -/
structure OrderCancelMessage where
  orderReferenceNumber : Alpha 9
  canceledShares : Alpha 6
  deriving DecidableEq, Repr

namespace OrderCancelMessage

def encode (message : OrderCancelMessage) : List UInt8 :=
  Alpha.encode message.orderReferenceNumber
    ++ (Alpha.encode message.canceledShares)

def decode (bytes : List UInt8) : Option (OrderCancelMessage × List UInt8) := do
  let (orderReferenceNumber, bytes) ← Alpha.decode 9 bytes
  let (canceledShares, bytes) ← Alpha.decode 6 bytes
  pure ({ orderReferenceNumber, canceledShares }, bytes)

@[simp] theorem encode_length (message : OrderCancelMessage) : (encode message).length = 15 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : OrderCancelMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderCancelMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderCancelMessage

/-- Trade Message: 41 bytes -/
structure TradeMessage where
  orderReferenceNumber : Alpha 9
  side : Side
  shares : Alpha 6
  stock : Alpha 6
  price : Alpha 10
  matchNumber : Alpha 9
  deriving DecidableEq, Repr

namespace TradeMessage

def encode (message : TradeMessage) : List UInt8 :=
  Alpha.encode message.orderReferenceNumber
    ++ (Side.encode message.side
    ++ (Alpha.encode message.shares
    ++ (Alpha.encode message.stock
    ++ (Alpha.encode message.price
    ++ (Alpha.encode message.matchNumber)))))

def decode (bytes : List UInt8) : Option (TradeMessage × List UInt8) := do
  let (orderReferenceNumber, bytes) ← Alpha.decode 9 bytes
  let (side, bytes) ← Side.decode bytes
  let (shares, bytes) ← Alpha.decode 6 bytes
  let (stock, bytes) ← Alpha.decode 6 bytes
  let (price, bytes) ← Alpha.decode 10 bytes
  let (matchNumber, bytes) ← Alpha.decode 9 bytes
  pure ({ orderReferenceNumber, side, shares, stock, price, matchNumber }, bytes)

@[simp] theorem encode_length (message : TradeMessage) : (encode message).length = 41 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, Side.encode_length]

theorem encode_length_pos (message : TradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end TradeMessage

/-- Broken Trade Message: 9 bytes -/
structure BrokenTradeMessage where
  matchNumber : Alpha 9
  deriving DecidableEq, Repr

namespace BrokenTradeMessage

def encode (message : BrokenTradeMessage) : List UInt8 :=
  Alpha.encode message.matchNumber

def decode (bytes : List UInt8) : Option (BrokenTradeMessage × List UInt8) := do
  let (matchNumber, bytes) ← Alpha.decode 9 bytes
  pure ({ matchNumber }, bytes)

@[simp] theorem encode_length (message : BrokenTradeMessage) : (encode message).length = 9 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : BrokenTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BrokenTradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end BrokenTradeMessage

/-- Stock Halt Status Message: 7 bytes -/
structure StockHaltStatusMessage where
  stock : Alpha 6
  stockHalted : StockHalted
  deriving DecidableEq, Repr

namespace StockHaltStatusMessage

def encode (message : StockHaltStatusMessage) : List UInt8 :=
  Alpha.encode message.stock
    ++ (StockHalted.encode message.stockHalted)

def decode (bytes : List UInt8) : Option (StockHaltStatusMessage × List UInt8) := do
  let (stock, bytes) ← Alpha.decode 6 bytes
  let (stockHalted, bytes) ← StockHalted.decode bytes
  pure ({ stock, stockHalted }, bytes)

@[simp] theorem encode_length (message : StockHaltStatusMessage) : (encode message).length = 7 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, StockHalted.encode_length]

theorem encode_length_pos (message : StockHaltStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StockHaltStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [StockHalted.decode_encode, some_bind]
  rfl

end StockHaltStatusMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | systemEventMessage (message : SystemEventMessage) -- "S" 0x53
  | addOrderMessage (message : AddOrderMessage) -- "A" 0x41
  | orderExecutedMessage (message : OrderExecutedMessage) -- "E" 0x45
  | orderCancelMessage (message : OrderCancelMessage) -- "X" 0x58
  | tradeMessage (message : TradeMessage) -- "P" 0x50
  | brokenTradeMessage (message : BrokenTradeMessage) -- "B" 0x42
  | stockHaltStatusMessage (message : StockHaltStatusMessage) -- "H" 0x48
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 8
  | .systemEventMessage _ => 83
  | .addOrderMessage _ => 65
  | .orderExecutedMessage _ => 69
  | .orderCancelMessage _ => 88
  | .tradeMessage _ => 80
  | .brokenTradeMessage _ => 66
  | .stockHaltStatusMessage _ => 72

def encode : Payload → List UInt8
  | .systemEventMessage message => SystemEventMessage.encode message
  | .addOrderMessage message => AddOrderMessage.encode message
  | .orderExecutedMessage message => OrderExecutedMessage.encode message
  | .orderCancelMessage message => OrderCancelMessage.encode message
  | .tradeMessage message => TradeMessage.encode message
  | .brokenTradeMessage message => BrokenTradeMessage.encode message
  | .stockHaltStatusMessage message => StockHaltStatusMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 41 := by
  cases message with
  | systemEventMessage inner =>
    simp only [encode, SystemEventMessage.encode_length]
    omega
  | addOrderMessage inner =>
    simp only [encode, AddOrderMessage.encode_length]
    omega
  | orderExecutedMessage inner =>
    simp only [encode, OrderExecutedMessage.encode_length]
    omega
  | orderCancelMessage inner =>
    simp only [encode, OrderCancelMessage.encode_length]
    omega
  | tradeMessage inner =>
    simp only [encode, TradeMessage.encode_length]
    omega
  | brokenTradeMessage inner =>
    simp only [encode, BrokenTradeMessage.encode_length]
    omega
  | stockHaltStatusMessage inner =>
    simp only [encode, StockHaltStatusMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 83 then (SystemEventMessage.decode bytes).map fun (message, rest) => (.systemEventMessage message, rest)
  else if tag = 65 then (AddOrderMessage.decode bytes).map fun (message, rest) => (.addOrderMessage message, rest)
  else if tag = 69 then (OrderExecutedMessage.decode bytes).map fun (message, rest) => (.orderExecutedMessage message, rest)
  else if tag = 88 then (OrderCancelMessage.decode bytes).map fun (message, rest) => (.orderCancelMessage message, rest)
  else if tag = 80 then (TradeMessage.decode bytes).map fun (message, rest) => (.tradeMessage message, rest)
  else if tag = 66 then (BrokenTradeMessage.decode bytes).map fun (message, rest) => (.brokenTradeMessage message, rest)
  else if tag = 72 then (StockHaltStatusMessage.decode bytes).map fun (message, rest) => (.stockHaltStatusMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Message Data -/
structure MessageData where
  timestamp : Alpha 8
  payload : Payload
  deriving DecidableEq, Repr

namespace MessageData

def encode (message : MessageData) : List UInt8 :=
  Alpha.encode message.timestamp
    ++ (encodeUInt 1 (Payload.tag message.payload)
    ++ (Payload.encode message.payload))

def decode (bytes : List UInt8) : Option (MessageData × List UInt8) := do
  let (timestamp, bytes) ← Alpha.decode 8 bytes
  let (messageType, bytes) ← decodeUInt 1 bytes
  let (payload, bytes) ← Payload.decode messageType bytes
  pure ({ timestamp, payload }, bytes)

theorem encode_length_pos (message : MessageData) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MessageData) : (encode message).length ≤ 50 := by
  unfold encode
  cases message.payload with
  | systemEventMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, SystemEventMessage.encode_length]
    omega
  | addOrderMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, AddOrderMessage.encode_length]
    omega
  | orderExecutedMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, OrderExecutedMessage.encode_length]
    omega
  | orderCancelMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, OrderCancelMessage.encode_length]
    omega
  | tradeMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, TradeMessage.encode_length]
    omega
  | brokenTradeMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, BrokenTradeMessage.encode_length]
    omega
  | stockHaltStatusMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUInt_length, StockHaltStatusMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : MessageData) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Payload.decode_encode, some_bind]
  rfl

end MessageData

/-- Any Message Body, selected by Message Length -/
inductive MessageBody where
  | endOfSession (message : EndOfSession) -- 0
  | messageData (message : Fallback MessageData.encode 16 [0]) -- any other value: the bytes it counts
  deriving DecidableEq, Repr

namespace MessageBody

/-- The Message Length each message is sent under -/
def tag : MessageBody → BitVec 16
  | .endOfSession _ => 0
  | .messageData message => message.key

def encode : MessageBody → List UInt8
  | .endOfSession message => EndOfSession.encode message
  | .messageData message => MessageData.encode message.val

/-- Does the message end the session? Nothing in its packet may follow it -/
def endsSession : MessageBody → Bool
  | .endOfSession _ => true
  | _ => false

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : MessageBody) : (encode message).length ≤ 50 := by
  cases message with
  | endOfSession inner =>
    simp only [encode, EndOfSession.encode_length]
    omega
  | messageData inner =>
    have bound_inner := MessageData.encode_length_le inner.val
    simp only [encode]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (MessageBody × List UInt8) :=
  if tag = 0 then (EndOfSession.decode bytes).map fun (message, rest) => (.endOfSession message, rest)
  else (decodeFallback 16 [0] MessageData.encode MessageData.decode tag.toNat bytes).map fun (message, rest) => (.messageData message, rest)

@[simp] theorem decode_encode (message : MessageBody) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message with
  | endOfSession m => simp [decode, encode, tag]
  | messageData m =>
    have unlisted_0 : m.key ≠ 0 := m.key_ne 0 (by decide) (by decide)
    dsimp only [decode, encode, tag]
    rw [ite_eq_right unlisted_0, decodeFallback_encode 16 [0] MessageData.encode MessageData.decode m (MessageData.decode_encode m.val)]
    rfl

end MessageBody

/-- Message -/
structure Message where
  messageBody : MessageBody
  deriving DecidableEq, Repr

namespace Message

def encode (message : Message) : List UInt8 :=
  encodeUIntLE 2 (MessageBody.tag message.messageBody)
    ++ (MessageBody.encode message.messageBody)

def decode (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (messageLength, bytes) ← decodeUIntLE 2 bytes
  let (messageBody, bytes) ← MessageBody.decode messageLength bytes
  pure ({ messageBody }, bytes)

theorem encode_length_pos (message : Message) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : Message) : (encode message).length ≤ 52 := by
  unfold encode
  cases message.messageBody with
  | endOfSession inner =>
    simp only [MessageBody.encode, List.length_append, encodeUIntLE_length, EndOfSession.encode_length]
    omega
  | messageData inner =>
    have bound_inner := MessageData.encode_length_le inner.val
    simp only [MessageBody.encode, List.length_append, encodeUIntLE_length]
    omega

@[simp] theorem decode_encode (message : Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [MessageBody.decode_encode, some_bind]
  rfl

/-- Does the message end the session? Nothing in its packet may follow it -/
def endsSession (message : Message) : Bool :=
  MessageBody.endsSession message.messageBody

end Message

/-- Packet -/
structure Packet where
  session : Alpha 10
  sequenceNumber : BitVec 32
  message : Bounded 2 Message
  message_last : endsLast Message.endsSession message.val = true
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  Alpha.encode message.session
    ++ (encodeUIntLE 4 message.sequenceNumber
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.message.val.length)
    ++ (encodeMany Message.encode message.message.val)))

def decode (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (session, bytes) ← Alpha.decode 10 bytes
  let (sequenceNumber, bytes) ← decodeUIntLE 4 bytes
  let (messageCount, bytes) ← decodeUIntLE 2 bytes
  let (message_, bytes) ← decodeMany Message.decode messageCount.toNat bytes
  if fits_message : message_.length < 256 ^ 2 then
    if last_message : endsLast Message.endsSession message_ = true then
      pure ({ session, sequenceNumber, message := ⟨message_, fits_message⟩, message_last := last_message }, bytes)
    else none
  else none

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : Packet) : (encode message).length ≤ 3407836 := by
  have bound_message := message.message.length_lt
  have bound_message_items := encodeMany_length_le Message.encode 52 Message.encode_length_le message.message.val
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUIntLE_length]
  omega

@[simp] theorem decode_encode (message : Packet) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 Message.encode Message.decode Message.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.message.length_lt, dite_eq_left message.message_last]
  rfl

end Packet

end Omi.NasdaqNsmequitiesTotalviewAsciiitchV20AUdp
