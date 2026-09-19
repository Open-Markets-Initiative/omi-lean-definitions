import Omi.Wire

/-!
# Imperative Execution Depth Of Book v1.11

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.ImperativeIntelligentcrossDepthofbookAspenV111

/-- Event: one byte code -/
def Event.codes : List UInt8 :=
  [0x4F, 0x53, 0x51, 0x45, 0x43]

inductive Event where
  | startOfSession -- Start Of Session
  | marketAcceptingOrders -- Market Accepting Orders
  | marketOpenForTrading -- Market Open For Trading
  | marketTradingEndedForDay -- Market Trading Ended For Day
  | endOfSession -- End Of Session
  | unlisted (byte : { byte : UInt8 // byte ∉ Event.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Event

def toByte : Event → UInt8
  | .startOfSession => 0x4F
  | .marketAcceptingOrders => 0x53
  | .marketOpenForTrading => 0x51
  | .marketTradingEndedForDay => 0x45
  | .endOfSession => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Event :=
  if byte = 0x4F then .startOfSession
  else if byte = 0x53 then .marketAcceptingOrders
  else if byte = 0x51 then .marketOpenForTrading
  else if byte = 0x45 then .marketTradingEndedForDay
  else .endOfSession

def ofByte (byte : UInt8) : Event :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Event) : ofByte value.toByte = value := by
  cases value with
  | startOfSession => decide
  | marketAcceptingOrders => decide
  | marketOpenForTrading => decide
  | marketTradingEndedForDay => decide
  | endOfSession => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : Event) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (Event × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : Event) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : Event) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end Event

/-- Listing Market: one byte code -/
def ListingMarket.codes : List UInt8 :=
  [0x4E, 0x51, 0x50, 0x5A, 0x41, 0x56]

inductive ListingMarket where
  | nyse -- Nyse
  | nasdaq -- Nasdaq
  | arca -- Arca
  | bats -- Bats
  | amex -- Amex
  | iex -- Iex
  | unlisted (byte : { byte : UInt8 // byte ∉ ListingMarket.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ListingMarket

def toByte : ListingMarket → UInt8
  | .nyse => 0x4E
  | .nasdaq => 0x51
  | .arca => 0x50
  | .bats => 0x5A
  | .amex => 0x41
  | .iex => 0x56
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ListingMarket :=
  if byte = 0x4E then .nyse
  else if byte = 0x51 then .nasdaq
  else if byte = 0x50 then .arca
  else if byte = 0x5A then .bats
  else if byte = 0x41 then .amex
  else .iex

def ofByte (byte : UInt8) : ListingMarket :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ListingMarket) : ofByte value.toByte = value := by
  cases value with
  | nyse => decide
  | nasdaq => decide
  | arca => decide
  | bats => decide
  | amex => decide
  | iex => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ListingMarket) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ListingMarket × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ListingMarket) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ListingMarket) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ListingMarket

/-- State: one byte code -/
def State.codes : List UInt8 :=
  [0x49, 0x41, 0x44, 0x45]

inductive State where
  | inactive -- Inactive
  | active -- Active
  | disabled -- Disabled
  | enabled -- Enabled
  | unlisted (byte : { byte : UInt8 // byte ∉ State.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace State

def toByte : State → UInt8
  | .inactive => 0x49
  | .active => 0x41
  | .disabled => 0x44
  | .enabled => 0x45
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : State :=
  if byte = 0x49 then .inactive
  else if byte = 0x41 then .active
  else if byte = 0x44 then .disabled
  else .enabled

def ofByte (byte : UInt8) : State :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : State) : ofByte value.toByte = value := by
  cases value with
  | inactive => decide
  | active => decide
  | disabled => decide
  | enabled => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : State) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (State × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : State) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : State) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end State

/-- Side: one byte code -/
def Side.codes : List UInt8 :=
  [0x42, 0x53, 0x43]

inductive Side where
  | buy -- Buy
  | sell -- Sell
  | endOfSession -- End Of Session
  | unlisted (byte : { byte : UInt8 // byte ∉ Side.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Side

def toByte : Side → UInt8
  | .buy => 0x42
  | .sell => 0x53
  | .endOfSession => 0x43
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Side :=
  if byte = 0x42 then .buy
  else if byte = 0x53 then .sell
  else .endOfSession

def ofByte (byte : UInt8) : Side :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Side) : ofByte value.toByte = value := by
  cases value with
  | buy => decide
  | sell => decide
  | endOfSession => decide
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

/-- Market Event Message: 11 bytes -/
structure MarketEventMessage where
  reserved2 : Alpha 2
  timestamp : BitVec 64
  event : Event
  deriving DecidableEq, Repr

namespace MarketEventMessage

def encode (message : MarketEventMessage) : List UInt8 :=
  Alpha.encode message.reserved2
    ++ (encodeUIntLE 8 message.timestamp
    ++ (Event.encode message.event))

def decode (bytes : List UInt8) : Option (MarketEventMessage × List UInt8) := do
  let (reserved2, bytes) ← Alpha.decode 2 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (event, bytes) ← Event.decode bytes
  pure ({ reserved2, timestamp, event }, bytes)

@[simp] theorem encode_length (message : MarketEventMessage) : (encode message).length = 11 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length, Event.encode_length]

theorem encode_length_pos (message : MarketEventMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketEventMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Event.decode_encode, some_bind]
  rfl

end MarketEventMessage

/-- Symbol Information Message: 27 bytes -/
structure SymbolInformationMessage where
  symbolId : BitVec 16
  timestamp : BitVec 64
  symbol : Alpha 11
  listingMarket : ListingMarket
  reserved1 : Alpha 1
  roundLotSize : BitVec 32
  deriving DecidableEq, Repr

namespace SymbolInformationMessage

def encode (message : SymbolInformationMessage) : List UInt8 :=
  encodeUIntLE 2 message.symbolId
    ++ (encodeUIntLE 8 message.timestamp
    ++ (Alpha.encode message.symbol
    ++ (ListingMarket.encode message.listingMarket
    ++ (Alpha.encode message.reserved1
    ++ (encodeUIntLE 4 message.roundLotSize)))))

def decode (bytes : List UInt8) : Option (SymbolInformationMessage × List UInt8) := do
  let (symbolId, bytes) ← decodeUIntLE 2 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (symbol, bytes) ← Alpha.decode 11 bytes
  let (listingMarket, bytes) ← ListingMarket.decode bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (roundLotSize, bytes) ← decodeUIntLE 4 bytes
  pure ({ symbolId, timestamp, symbol, listingMarket, reserved1, roundLotSize }, bytes)

@[simp] theorem encode_length (message : SymbolInformationMessage) : (encode message).length = 27 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, ListingMarket.encode_length]

theorem encode_length_pos (message : SymbolInformationMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SymbolInformationMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ListingMarket.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SymbolInformationMessage

/-- Symbol State Message: 27 bytes -/
structure SymbolStateMessage where
  symbolId : BitVec 16
  timestamp : BitVec 64
  symbol : Alpha 11
  state : State
  reserved1 : Alpha 1
  info : Alpha 4
  deriving DecidableEq, Repr

namespace SymbolStateMessage

def encode (message : SymbolStateMessage) : List UInt8 :=
  encodeUIntLE 2 message.symbolId
    ++ (encodeUIntLE 8 message.timestamp
    ++ (Alpha.encode message.symbol
    ++ (State.encode message.state
    ++ (Alpha.encode message.reserved1
    ++ (Alpha.encode message.info)))))

def decode (bytes : List UInt8) : Option (SymbolStateMessage × List UInt8) := do
  let (symbolId, bytes) ← decodeUIntLE 2 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (symbol, bytes) ← Alpha.decode 11 bytes
  let (state, bytes) ← State.decode bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (info, bytes) ← Alpha.decode 4 bytes
  pure ({ symbolId, timestamp, symbol, state, reserved1, info }, bytes)

@[simp] theorem encode_length (message : SymbolStateMessage) : (encode message).length = 27 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, State.encode_length]

theorem encode_length_pos (message : SymbolStateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SymbolStateMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, State.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SymbolStateMessage

/-- New Order Add Message: 46 bytes -/
structure NewOrderAddMessage where
  symbolId : BitVec 16
  timestamp : BitVec 64
  orderId : BitVec 64
  side : Side
  shares : BitVec 32
  symbol : Alpha 11
  price : BitVec 64
  reserved4 : Alpha 4
  deriving DecidableEq, Repr

namespace NewOrderAddMessage

def encode (message : NewOrderAddMessage) : List UInt8 :=
  encodeUIntLE 2 message.symbolId
    ++ (encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.orderId
    ++ (Side.encode message.side
    ++ (encodeUIntLE 4 message.shares
    ++ (Alpha.encode message.symbol
    ++ (encodeUIntLE 8 message.price
    ++ (Alpha.encode message.reserved4)))))))

def decode (bytes : List UInt8) : Option (NewOrderAddMessage × List UInt8) := do
  let (symbolId, bytes) ← decodeUIntLE 2 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (side, bytes) ← Side.decode bytes
  let (shares, bytes) ← decodeUIntLE 4 bytes
  let (symbol, bytes) ← Alpha.decode 11 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (reserved4, bytes) ← Alpha.decode 4 bytes
  pure ({ symbolId, timestamp, orderId, side, shares, symbol, price, reserved4 }, bytes)

@[simp] theorem encode_length (message : NewOrderAddMessage) : (encode message).length = 46 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Side.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : NewOrderAddMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NewOrderAddMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end NewOrderAddMessage

/-- Order Partial Cancel Message: 22 bytes -/
structure OrderPartialCancelMessage where
  symbolId : BitVec 16
  timestamp : BitVec 64
  orderId : BitVec 64
  sharesCanceled : BitVec 32
  deriving DecidableEq, Repr

namespace OrderPartialCancelMessage

def encode (message : OrderPartialCancelMessage) : List UInt8 :=
  encodeUIntLE 2 message.symbolId
    ++ (encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 4 message.sharesCanceled)))

def decode (bytes : List UInt8) : Option (OrderPartialCancelMessage × List UInt8) := do
  let (symbolId, bytes) ← decodeUIntLE 2 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (sharesCanceled, bytes) ← decodeUIntLE 4 bytes
  pure ({ symbolId, timestamp, orderId, sharesCanceled }, bytes)

@[simp] theorem encode_length (message : OrderPartialCancelMessage) : (encode message).length = 22 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : OrderPartialCancelMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderPartialCancelMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OrderPartialCancelMessage

/-- Order Cancel All Message: 18 bytes -/
structure OrderCancelAllMessage where
  symbolId : BitVec 16
  timestamp : BitVec 64
  orderId : BitVec 64
  deriving DecidableEq, Repr

namespace OrderCancelAllMessage

def encode (message : OrderCancelAllMessage) : List UInt8 :=
  encodeUIntLE 2 message.symbolId
    ++ (encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.orderId))

def decode (bytes : List UInt8) : Option (OrderCancelAllMessage × List UInt8) := do
  let (symbolId, bytes) ← decodeUIntLE 2 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  pure ({ symbolId, timestamp, orderId }, bytes)

@[simp] theorem encode_length (message : OrderCancelAllMessage) : (encode message).length = 18 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : OrderCancelAllMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderCancelAllMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OrderCancelAllMessage

/-- Order Updated Message: 30 bytes -/
structure OrderUpdatedMessage where
  symbolId : BitVec 16
  timestamp : BitVec 64
  orderId : BitVec 64
  shares : BitVec 32
  price : BitVec 64
  deriving DecidableEq, Repr

namespace OrderUpdatedMessage

def encode (message : OrderUpdatedMessage) : List UInt8 :=
  encodeUIntLE 2 message.symbolId
    ++ (encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 4 message.shares
    ++ (encodeUIntLE 8 message.price))))

def decode (bytes : List UInt8) : Option (OrderUpdatedMessage × List UInt8) := do
  let (symbolId, bytes) ← decodeUIntLE 2 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (shares, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  pure ({ symbolId, timestamp, orderId, shares, price }, bytes)

@[simp] theorem encode_length (message : OrderUpdatedMessage) : (encode message).length = 30 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : OrderUpdatedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderUpdatedMessage) (rest : List UInt8) :
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OrderUpdatedMessage

/-- Order Executed Message: 39 bytes -/
structure OrderExecutedMessage where
  symbolId : BitVec 16
  timestamp : BitVec 64
  orderId : BitVec 64
  shares : BitVec 32
  executionId : BitVec 64
  reserved1 : Alpha 1
  price : BitVec 64
  deriving DecidableEq, Repr

namespace OrderExecutedMessage

def encode (message : OrderExecutedMessage) : List UInt8 :=
  encodeUIntLE 2 message.symbolId
    ++ (encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 4 message.shares
    ++ (encodeUIntLE 8 message.executionId
    ++ (Alpha.encode message.reserved1
    ++ (encodeUIntLE 8 message.price))))))

def decode (bytes : List UInt8) : Option (OrderExecutedMessage × List UInt8) := do
  let (symbolId, bytes) ← decodeUIntLE 2 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (shares, bytes) ← decodeUIntLE 4 bytes
  let (executionId, bytes) ← decodeUIntLE 8 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  pure ({ symbolId, timestamp, orderId, shares, executionId, reserved1, price }, bytes)

@[simp] theorem encode_length (message : OrderExecutedMessage) : (encode message).length = 39 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : OrderExecutedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderExecutedMessage) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OrderExecutedMessage

/-- Trade Message: 50 bytes -/
structure TradeMessage where
  symbolId : BitVec 16
  timestamp : BitVec 64
  reserved8 : BitVec 64
  reserved1 : Alpha 1
  shares : BitVec 32
  symbol : Alpha 11
  price : BitVec 64
  executionId : BitVec 64
  deriving DecidableEq, Repr

namespace TradeMessage

def encode (message : TradeMessage) : List UInt8 :=
  encodeUIntLE 2 message.symbolId
    ++ (encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.reserved8
    ++ (Alpha.encode message.reserved1
    ++ (encodeUIntLE 4 message.shares
    ++ (Alpha.encode message.symbol
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 8 message.executionId)))))))

def decode (bytes : List UInt8) : Option (TradeMessage × List UInt8) := do
  let (symbolId, bytes) ← decodeUIntLE 2 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (reserved8, bytes) ← decodeUIntLE 8 bytes
  let (reserved1, bytes) ← Alpha.decode 1 bytes
  let (shares, bytes) ← decodeUIntLE 4 bytes
  let (symbol, bytes) ← Alpha.decode 11 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (executionId, bytes) ← decodeUIntLE 8 bytes
  pure ({ symbolId, timestamp, reserved8, reserved1, shares, symbol, price, executionId }, bytes)

@[simp] theorem encode_length (message : TradeMessage) : (encode message).length = 50 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : TradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TradeMessage

/-- Trade Break Message: 18 bytes -/
structure TradeBreakMessage where
  symbolId : BitVec 16
  timestamp : BitVec 64
  executionId : BitVec 64
  deriving DecidableEq, Repr

namespace TradeBreakMessage

def encode (message : TradeBreakMessage) : List UInt8 :=
  encodeUIntLE 2 message.symbolId
    ++ (encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 8 message.executionId))

def decode (bytes : List UInt8) : Option (TradeBreakMessage × List UInt8) := do
  let (symbolId, bytes) ← decodeUIntLE 2 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (executionId, bytes) ← decodeUIntLE 8 bytes
  pure ({ symbolId, timestamp, executionId }, bytes)

@[simp] theorem encode_length (message : TradeBreakMessage) : (encode message).length = 18 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : TradeBreakMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeBreakMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TradeBreakMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | marketEventMessage (message : MarketEventMessage) -- 'A' 0x41
  | symbolInformationMessage (message : SymbolInformationMessage) -- 'B' 0x42
  | symbolStateMessage (message : SymbolStateMessage) -- 'C' 0x43
  | newOrderAddMessage (message : NewOrderAddMessage) -- 'D' 0x44
  | orderPartialCancelMessage (message : OrderPartialCancelMessage) -- 'F' 0x46
  | orderCancelAllMessage (message : OrderCancelAllMessage) -- 'G' 0x47
  | orderUpdatedMessage (message : OrderUpdatedMessage) -- 'H' 0x48
  | orderExecutedMessage (message : OrderExecutedMessage) -- 'J' 0x4A
  | tradeMessage (message : TradeMessage) -- 'K' 0x4B
  | tradeBreakMessage (message : TradeBreakMessage) -- 'M' 0x4D
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 8
  | .marketEventMessage _ => 65
  | .symbolInformationMessage _ => 66
  | .symbolStateMessage _ => 67
  | .newOrderAddMessage _ => 68
  | .orderPartialCancelMessage _ => 70
  | .orderCancelAllMessage _ => 71
  | .orderUpdatedMessage _ => 72
  | .orderExecutedMessage _ => 74
  | .tradeMessage _ => 75
  | .tradeBreakMessage _ => 77

def encode : Payload → List UInt8
  | .marketEventMessage message => MarketEventMessage.encode message
  | .symbolInformationMessage message => SymbolInformationMessage.encode message
  | .symbolStateMessage message => SymbolStateMessage.encode message
  | .newOrderAddMessage message => NewOrderAddMessage.encode message
  | .orderPartialCancelMessage message => OrderPartialCancelMessage.encode message
  | .orderCancelAllMessage message => OrderCancelAllMessage.encode message
  | .orderUpdatedMessage message => OrderUpdatedMessage.encode message
  | .orderExecutedMessage message => OrderExecutedMessage.encode message
  | .tradeMessage message => TradeMessage.encode message
  | .tradeBreakMessage message => TradeBreakMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 50 := by
  cases message with
  | marketEventMessage inner =>
    simp only [encode, MarketEventMessage.encode_length]
    omega
  | symbolInformationMessage inner =>
    simp only [encode, SymbolInformationMessage.encode_length]
    omega
  | symbolStateMessage inner =>
    simp only [encode, SymbolStateMessage.encode_length]
    omega
  | newOrderAddMessage inner =>
    simp only [encode, NewOrderAddMessage.encode_length]
    omega
  | orderPartialCancelMessage inner =>
    simp only [encode, OrderPartialCancelMessage.encode_length]
    omega
  | orderCancelAllMessage inner =>
    simp only [encode, OrderCancelAllMessage.encode_length]
    omega
  | orderUpdatedMessage inner =>
    simp only [encode, OrderUpdatedMessage.encode_length]
    omega
  | orderExecutedMessage inner =>
    simp only [encode, OrderExecutedMessage.encode_length]
    omega
  | tradeMessage inner =>
    simp only [encode, TradeMessage.encode_length]
    omega
  | tradeBreakMessage inner =>
    simp only [encode, TradeBreakMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 65 then (MarketEventMessage.decode bytes).map fun (message, rest) => (.marketEventMessage message, rest)
  else if tag = 66 then (SymbolInformationMessage.decode bytes).map fun (message, rest) => (.symbolInformationMessage message, rest)
  else if tag = 67 then (SymbolStateMessage.decode bytes).map fun (message, rest) => (.symbolStateMessage message, rest)
  else if tag = 68 then (NewOrderAddMessage.decode bytes).map fun (message, rest) => (.newOrderAddMessage message, rest)
  else if tag = 70 then (OrderPartialCancelMessage.decode bytes).map fun (message, rest) => (.orderPartialCancelMessage message, rest)
  else if tag = 71 then (OrderCancelAllMessage.decode bytes).map fun (message, rest) => (.orderCancelAllMessage message, rest)
  else if tag = 72 then (OrderUpdatedMessage.decode bytes).map fun (message, rest) => (.orderUpdatedMessage message, rest)
  else if tag = 74 then (OrderExecutedMessage.decode bytes).map fun (message, rest) => (.orderExecutedMessage message, rest)
  else if tag = 75 then (TradeMessage.decode bytes).map fun (message, rest) => (.tradeMessage message, rest)
  else if tag = 77 then (TradeBreakMessage.decode bytes).map fun (message, rest) => (.tradeBreakMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Message -/
structure Message where
  length : BitVec 16
  payload : Payload
  deriving DecidableEq, Repr

namespace Message

def encode (message : Message) : List UInt8 :=
  encodeUIntLE 2 message.length
    ++ (encodeUInt 1 (Payload.tag message.payload)
    ++ (Payload.encode message.payload))

def decode (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (length, bytes) ← decodeUIntLE 2 bytes
  let (messageType, bytes) ← decodeUInt 1 bytes
  let (payload, bytes) ← Payload.decode messageType bytes
  pure ({ length, payload }, bytes)

theorem encode_length_pos (message : Message) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : Message) : (encode message).length ≤ 53 := by
  unfold encode
  cases message.payload with
  | marketEventMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, MarketEventMessage.encode_length]
    omega
  | symbolInformationMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, SymbolInformationMessage.encode_length]
    omega
  | symbolStateMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, SymbolStateMessage.encode_length]
    omega
  | newOrderAddMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, NewOrderAddMessage.encode_length]
    omega
  | orderPartialCancelMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, OrderPartialCancelMessage.encode_length]
    omega
  | orderCancelAllMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, OrderCancelAllMessage.encode_length]
    omega
  | orderUpdatedMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, OrderUpdatedMessage.encode_length]
    omega
  | orderExecutedMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, OrderExecutedMessage.encode_length]
    omega
  | tradeMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, TradeMessage.encode_length]
    omega
  | tradeBreakMessage inner =>
    simp only [Payload.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, TradeBreakMessage.encode_length]
    omega

@[simp] theorem decode_encode (message : Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Payload.decode_encode, some_bind]
  rfl

end Message

/-- Packet -/
structure Packet where
  marketDayIdentifier : Alpha 9
  feedIdentifier : Alpha 1
  sequence : BitVec 64
  message : Bounded 2 Message
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  Alpha.encode message.marketDayIdentifier
    ++ (Alpha.encode message.feedIdentifier
    ++ (encodeUIntLE 8 message.sequence
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.message.val.length)
    ++ (encodeMany Message.encode message.message.val))))

def decode (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (marketDayIdentifier, bytes) ← Alpha.decode 9 bytes
  let (feedIdentifier, bytes) ← Alpha.decode 1 bytes
  let (sequence, bytes) ← decodeUIntLE 8 bytes
  let (count, bytes) ← decodeUIntLE 2 bytes
  let (message_, bytes) ← decodeMany Message.decode count.toNat bytes
  if fits_message : message_.length < 256 ^ 2 then
    pure ({ marketDayIdentifier, feedIdentifier, sequence, message := ⟨message_, fits_message⟩ }, bytes)
  else none

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : Packet) : (encode message).length ≤ 3473375 := by
  have bound_message := message.message.length_lt
  have bound_message_items := encodeMany_length_le Message.encode 53 Message.encode_length_le message.message.val
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, encodeUIntLE_length]
  omega

@[simp] theorem decode_encode (message : Packet) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 Message.encode Message.decode Message.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.message.length_lt]
  rfl

end Packet

end Omi.ImperativeIntelligentcrossDepthofbookAspenV111
