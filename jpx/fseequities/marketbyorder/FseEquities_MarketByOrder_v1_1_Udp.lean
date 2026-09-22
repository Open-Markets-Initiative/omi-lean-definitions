import Omi.Wire

/-!
# Japan Exchange Group Market By Order v1.1

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.JpxFseequitiesMarketbyorderFlexV11Udp

/-- Triggered Side: one byte code -/
def TriggeredSide.codes : List UInt8 :=
  [0x53, 0x42, 0x20]

inductive TriggeredSide where
  | sellOrder -- Sell Order
  | buyOrder -- Buy Order
  | itayoseExecution -- Itayose Execution
  | unlisted (byte : { byte : UInt8 // byte ∉ TriggeredSide.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace TriggeredSide

def toByte : TriggeredSide → UInt8
  | .sellOrder => 0x53
  | .buyOrder => 0x42
  | .itayoseExecution => 0x20
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : TriggeredSide :=
  if byte = 0x53 then .sellOrder
  else if byte = 0x42 then .buyOrder
  else .itayoseExecution

def ofByte (byte : UInt8) : TriggeredSide :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : TriggeredSide) : ofByte value.toByte = value := by
  cases value with
  | sellOrder => decide
  | buyOrder => decide
  | itayoseExecution => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : TriggeredSide) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (TriggeredSide × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : TriggeredSide) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : TriggeredSide) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end TriggeredSide

/-- Side: one byte code -/
def Side.codes : List UInt8 :=
  [0x53, 0x42]

inductive Side where
  | sellOrder -- Sell Order
  | buyOrder -- Buy Order
  | unlisted (byte : { byte : UInt8 // byte ∉ Side.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace Side

def toByte : Side → UInt8
  | .sellOrder => 0x53
  | .buyOrder => 0x42
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : Side :=
  if byte = 0x53 then .sellOrder
  else .buyOrder

def ofByte (byte : UInt8) : Side :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : Side) : ofByte value.toByte = value := by
  cases value with
  | sellOrder => decide
  | buyOrder => decide
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

/-- Seconds Timestamp Message: 4 bytes -/
structure SecondsTimestampMessage where
  timeSeconds : BitVec 32
  deriving DecidableEq, Repr

namespace SecondsTimestampMessage

def encode (message : SecondsTimestampMessage) : List UInt8 :=
  encodeUInt 4 message.timeSeconds

def decode (bytes : List UInt8) : Option (SecondsTimestampMessage × List UInt8) := do
  let (timeSeconds, bytes) ← decodeUInt 4 bytes
  pure ({ timeSeconds }, bytes)

@[simp] theorem encode_length (message : SecondsTimestampMessage) : (encode message).length = 4 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : SecondsTimestampMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecondsTimestampMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SecondsTimestampMessage

/-- Trading Status Message: 17 bytes -/
structure TradingStatusMessage where
  timeMicroseconds : BitVec 32
  marketStatus : BitVec 8
  statusFlag : Alpha 2
  shortSellingStatus : BitVec 8
  pricingMethod : BitVec 8
  bookCenterPrice : BitVec 64
  deriving DecidableEq, Repr

namespace TradingStatusMessage

def encode (message : TradingStatusMessage) : List UInt8 :=
  encodeUInt 4 message.timeMicroseconds
    ++ (encodeUInt 1 message.marketStatus
    ++ (Alpha.encode message.statusFlag
    ++ (encodeUInt 1 message.shortSellingStatus
    ++ (encodeUInt 1 message.pricingMethod
    ++ (encodeUInt 8 message.bookCenterPrice)))))

def decode (bytes : List UInt8) : Option (TradingStatusMessage × List UInt8) := do
  let (timeMicroseconds, bytes) ← decodeUInt 4 bytes
  let (marketStatus, bytes) ← decodeUInt 1 bytes
  let (statusFlag, bytes) ← Alpha.decode 2 bytes
  let (shortSellingStatus, bytes) ← decodeUInt 1 bytes
  let (pricingMethod, bytes) ← decodeUInt 1 bytes
  let (bookCenterPrice, bytes) ← decodeUInt 8 bytes
  pure ({ timeMicroseconds, marketStatus, statusFlag, shortSellingStatus, pricingMethod, bookCenterPrice }, bytes)

@[simp] theorem encode_length (message : TradingStatusMessage) : (encode message).length = 17 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : TradingStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradingStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end TradingStatusMessage

/-- Execution Summary Message: 45 bytes -/
structure ExecutionSummaryMessage where
  timeMicroseconds : BitVec 32
  triggeredSide : TriggeredSide
  totalVolume : BitVec 48
  totalInvalidation : BitVec 48
  lastPrice : BitVec 64
  matchId : BitVec 32
  bestOffer : BitVec 64
  bestBid : BitVec 64
  deriving DecidableEq, Repr

namespace ExecutionSummaryMessage

def encode (message : ExecutionSummaryMessage) : List UInt8 :=
  encodeUInt 4 message.timeMicroseconds
    ++ (TriggeredSide.encode message.triggeredSide
    ++ (encodeUInt 6 message.totalVolume
    ++ (encodeUInt 6 message.totalInvalidation
    ++ (encodeUInt 8 message.lastPrice
    ++ (encodeUInt 4 message.matchId
    ++ (encodeUInt 8 message.bestOffer
    ++ (encodeUInt 8 message.bestBid)))))))

def decode (bytes : List UInt8) : Option (ExecutionSummaryMessage × List UInt8) := do
  let (timeMicroseconds, bytes) ← decodeUInt 4 bytes
  let (triggeredSide, bytes) ← TriggeredSide.decode bytes
  let (totalVolume, bytes) ← decodeUInt 6 bytes
  let (totalInvalidation, bytes) ← decodeUInt 6 bytes
  let (lastPrice, bytes) ← decodeUInt 8 bytes
  let (matchId, bytes) ← decodeUInt 4 bytes
  let (bestOffer, bytes) ← decodeUInt 8 bytes
  let (bestBid, bytes) ← decodeUInt 8 bytes
  pure ({ timeMicroseconds, triggeredSide, totalVolume, totalInvalidation, lastPrice, matchId, bestOffer, bestBid }, bytes)

@[simp] theorem encode_length (message : ExecutionSummaryMessage) : (encode message).length = 45 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, TriggeredSide.encode_length]

theorem encode_length_pos (message : ExecutionSummaryMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ExecutionSummaryMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, TriggeredSide.decode_encode, some_bind]
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ExecutionSummaryMessage

/-- Add Order Message: 25 bytes -/
structure AddOrderMessage where
  timeMicroseconds : BitVec 32
  orderId : BitVec 32
  side : Side
  quantity : BitVec 48
  price : BitVec 64
  orderCondition : BitVec 8
  modificationFlag : BitVec 8
  deriving DecidableEq, Repr

namespace AddOrderMessage

def encode (message : AddOrderMessage) : List UInt8 :=
  encodeUInt 4 message.timeMicroseconds
    ++ (encodeUInt 4 message.orderId
    ++ (Side.encode message.side
    ++ (encodeUInt 6 message.quantity
    ++ (encodeUInt 8 message.price
    ++ (encodeUInt 1 message.orderCondition
    ++ (encodeUInt 1 message.modificationFlag))))))

def decode (bytes : List UInt8) : Option (AddOrderMessage × List UInt8) := do
  let (timeMicroseconds, bytes) ← decodeUInt 4 bytes
  let (orderId, bytes) ← decodeUInt 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (quantity, bytes) ← decodeUInt 6 bytes
  let (price, bytes) ← decodeUInt 8 bytes
  let (orderCondition, bytes) ← decodeUInt 1 bytes
  let (modificationFlag, bytes) ← decodeUInt 1 bytes
  pure ({ timeMicroseconds, orderId, side, quantity, price, orderCondition, modificationFlag }, bytes)

@[simp] theorem encode_length (message : AddOrderMessage) : (encode message).length = 25 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Side.encode_length]

theorem encode_length_pos (message : AddOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AddOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end AddOrderMessage

/-- Order Executed Message: 19 bytes -/
structure OrderExecutedMessage where
  timeMicroseconds : BitVec 32
  orderId : BitVec 32
  side : Side
  volume : BitVec 48
  matchId : BitVec 32
  deriving DecidableEq, Repr

namespace OrderExecutedMessage

def encode (message : OrderExecutedMessage) : List UInt8 :=
  encodeUInt 4 message.timeMicroseconds
    ++ (encodeUInt 4 message.orderId
    ++ (Side.encode message.side
    ++ (encodeUInt 6 message.volume
    ++ (encodeUInt 4 message.matchId))))

def decode (bytes : List UInt8) : Option (OrderExecutedMessage × List UInt8) := do
  let (timeMicroseconds, bytes) ← decodeUInt 4 bytes
  let (orderId, bytes) ← decodeUInt 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (volume, bytes) ← decodeUInt 6 bytes
  let (matchId, bytes) ← decodeUInt 4 bytes
  pure ({ timeMicroseconds, orderId, side, volume, matchId }, bytes)

@[simp] theorem encode_length (message : OrderExecutedMessage) : (encode message).length = 19 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Side.encode_length]

theorem encode_length_pos (message : OrderExecutedMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderExecutedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderExecutedMessage

/-- Order Executed With Price Message: 28 bytes -/
structure OrderExecutedWithPriceMessage where
  timeMicroseconds : BitVec 32
  orderId : BitVec 32
  side : Side
  volume : BitVec 48
  matchId : BitVec 32
  executionPrice : BitVec 64
  adoptedPricingMethod : BitVec 8
  deriving DecidableEq, Repr

namespace OrderExecutedWithPriceMessage

def encode (message : OrderExecutedWithPriceMessage) : List UInt8 :=
  encodeUInt 4 message.timeMicroseconds
    ++ (encodeUInt 4 message.orderId
    ++ (Side.encode message.side
    ++ (encodeUInt 6 message.volume
    ++ (encodeUInt 4 message.matchId
    ++ (encodeUInt 8 message.executionPrice
    ++ (encodeUInt 1 message.adoptedPricingMethod))))))

def decode (bytes : List UInt8) : Option (OrderExecutedWithPriceMessage × List UInt8) := do
  let (timeMicroseconds, bytes) ← decodeUInt 4 bytes
  let (orderId, bytes) ← decodeUInt 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (volume, bytes) ← decodeUInt 6 bytes
  let (matchId, bytes) ← decodeUInt 4 bytes
  let (executionPrice, bytes) ← decodeUInt 8 bytes
  let (adoptedPricingMethod, bytes) ← decodeUInt 1 bytes
  pure ({ timeMicroseconds, orderId, side, volume, matchId, executionPrice, adoptedPricingMethod }, bytes)

@[simp] theorem encode_length (message : OrderExecutedWithPriceMessage) : (encode message).length = 28 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Side.encode_length]

theorem encode_length_pos (message : OrderExecutedWithPriceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderExecutedWithPriceMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderExecutedWithPriceMessage

/-- Order Delete Message: 10 bytes -/
structure OrderDeleteMessage where
  timeMicroseconds : BitVec 32
  orderId : BitVec 32
  side : Side
  modificationFlag : BitVec 8
  deriving DecidableEq, Repr

namespace OrderDeleteMessage

def encode (message : OrderDeleteMessage) : List UInt8 :=
  encodeUInt 4 message.timeMicroseconds
    ++ (encodeUInt 4 message.orderId
    ++ (Side.encode message.side
    ++ (encodeUInt 1 message.modificationFlag)))

def decode (bytes : List UInt8) : Option (OrderDeleteMessage × List UInt8) := do
  let (timeMicroseconds, bytes) ← decodeUInt 4 bytes
  let (orderId, bytes) ← decodeUInt 4 bytes
  let (side, bytes) ← Side.decode bytes
  let (modificationFlag, bytes) ← decodeUInt 1 bytes
  pure ({ timeMicroseconds, orderId, side, modificationFlag }, bytes)

@[simp] theorem encode_length (message : OrderDeleteMessage) : (encode message).length = 10 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Side.encode_length]

theorem encode_length_pos (message : OrderDeleteMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderDeleteMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Side.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end OrderDeleteMessage

/-- Reset Message: 1 bytes -/
structure ResetMessage where
  resetStartEndFlag : BitVec 8
  deriving DecidableEq, Repr

namespace ResetMessage

def encode (message : ResetMessage) : List UInt8 :=
  encodeUInt 1 message.resetStartEndFlag

def decode (bytes : List UInt8) : Option (ResetMessage × List UInt8) := do
  let (resetStartEndFlag, bytes) ← decodeUInt 1 bytes
  pure ({ resetStartEndFlag }, bytes)

@[simp] theorem encode_length (message : ResetMessage) : (encode message).length = 1 := by
  unfold encode
  simp only [encodeUInt_length]

theorem encode_length_pos (message : ResetMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ResetMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ResetMessage

/-- Communication Control Message: 2 bytes -/
structure CommunicationControlMessage where
  testModeFlag : BitVec 8
  communicationStartEndFlag : BitVec 8
  deriving DecidableEq, Repr

namespace CommunicationControlMessage

def encode (message : CommunicationControlMessage) : List UInt8 :=
  encodeUInt 1 message.testModeFlag
    ++ (encodeUInt 1 message.communicationStartEndFlag)

def decode (bytes : List UInt8) : Option (CommunicationControlMessage × List UInt8) := do
  let (testModeFlag, bytes) ← decodeUInt 1 bytes
  let (communicationStartEndFlag, bytes) ← decodeUInt 1 bytes
  pure ({ testModeFlag, communicationStartEndFlag }, bytes)

@[simp] theorem encode_length (message : CommunicationControlMessage) : (encode message).length = 2 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length]

theorem encode_length_pos (message : CommunicationControlMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CommunicationControlMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end CommunicationControlMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | secondsTimestampMessage (message : SecondsTimestampMessage) -- "T" 0x54
  | tradingStatusMessage (message : TradingStatusMessage) -- "O" 0x4F
  | executionSummaryMessage (message : ExecutionSummaryMessage) -- "K" 0x4B
  | addOrderMessage (message : AddOrderMessage) -- "A" 0x41
  | orderExecutedMessage (message : OrderExecutedMessage) -- "E" 0x45
  | orderExecutedWithPriceMessage (message : OrderExecutedWithPriceMessage) -- "C" 0x43
  | orderDeleteMessage (message : OrderDeleteMessage) -- "D" 0x44
  | resetMessage (message : ResetMessage) -- "R" 0x52
  | communicationControlMessage (message : CommunicationControlMessage) -- "L" 0x4C
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 8
  | .secondsTimestampMessage _ => 84
  | .tradingStatusMessage _ => 79
  | .executionSummaryMessage _ => 75
  | .addOrderMessage _ => 65
  | .orderExecutedMessage _ => 69
  | .orderExecutedWithPriceMessage _ => 67
  | .orderDeleteMessage _ => 68
  | .resetMessage _ => 82
  | .communicationControlMessage _ => 76

def encode : Payload → List UInt8
  | .secondsTimestampMessage message => SecondsTimestampMessage.encode message
  | .tradingStatusMessage message => TradingStatusMessage.encode message
  | .executionSummaryMessage message => ExecutionSummaryMessage.encode message
  | .addOrderMessage message => AddOrderMessage.encode message
  | .orderExecutedMessage message => OrderExecutedMessage.encode message
  | .orderExecutedWithPriceMessage message => OrderExecutedWithPriceMessage.encode message
  | .orderDeleteMessage message => OrderDeleteMessage.encode message
  | .resetMessage message => ResetMessage.encode message
  | .communicationControlMessage message => CommunicationControlMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 45 := by
  cases message with
  | secondsTimestampMessage inner =>
    simp only [encode, SecondsTimestampMessage.encode_length]
    omega
  | tradingStatusMessage inner =>
    simp only [encode, TradingStatusMessage.encode_length]
    omega
  | executionSummaryMessage inner =>
    simp only [encode, ExecutionSummaryMessage.encode_length]
    omega
  | addOrderMessage inner =>
    simp only [encode, AddOrderMessage.encode_length]
    omega
  | orderExecutedMessage inner =>
    simp only [encode, OrderExecutedMessage.encode_length]
    omega
  | orderExecutedWithPriceMessage inner =>
    simp only [encode, OrderExecutedWithPriceMessage.encode_length]
    omega
  | orderDeleteMessage inner =>
    simp only [encode, OrderDeleteMessage.encode_length]
    omega
  | resetMessage inner =>
    simp only [encode, ResetMessage.encode_length]
    omega
  | communicationControlMessage inner =>
    simp only [encode, CommunicationControlMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 84 then (SecondsTimestampMessage.decode bytes).map fun (message, rest) => (.secondsTimestampMessage message, rest)
  else if tag = 79 then (TradingStatusMessage.decode bytes).map fun (message, rest) => (.tradingStatusMessage message, rest)
  else if tag = 75 then (ExecutionSummaryMessage.decode bytes).map fun (message, rest) => (.executionSummaryMessage message, rest)
  else if tag = 65 then (AddOrderMessage.decode bytes).map fun (message, rest) => (.addOrderMessage message, rest)
  else if tag = 69 then (OrderExecutedMessage.decode bytes).map fun (message, rest) => (.orderExecutedMessage message, rest)
  else if tag = 67 then (OrderExecutedWithPriceMessage.decode bytes).map fun (message, rest) => (.orderExecutedWithPriceMessage message, rest)
  else if tag = 68 then (OrderDeleteMessage.decode bytes).map fun (message, rest) => (.orderDeleteMessage message, rest)
  else if tag = 82 then (ResetMessage.decode bytes).map fun (message, rest) => (.resetMessage message, rest)
  else if tag = 76 then (CommunicationControlMessage.decode bytes).map fun (message, rest) => (.communicationControlMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Message -/
structure Message where
  payload : Payload
  deriving DecidableEq, Repr

namespace Message

def encodeBody (message : Message) : List UInt8 :=
  encodeUInt 1 (Payload.tag message.payload)
    ++ (Payload.encode message.payload)

def decodeBody (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (messageType, bytes) ← decodeUInt 1 bytes
  let (payload, bytes) ← Payload.decode messageType bytes
  pure ({ payload }, bytes)

theorem decodeBody_encodeBody (message : Message) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Payload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : Message) : (encodeBody message).length + 0 < 256 ^ 1 := by
  unfold encodeBody
  cases message.payload with
  | secondsTimestampMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SecondsTimestampMessage.encode_length]
    omega
  | tradingStatusMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TradingStatusMessage.encode_length]
    omega
  | executionSummaryMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ExecutionSummaryMessage.encode_length]
    omega
  | addOrderMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, AddOrderMessage.encode_length]
    omega
  | orderExecutedMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderExecutedMessage.encode_length]
    omega
  | orderExecutedWithPriceMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderExecutedWithPriceMessage.encode_length]
    omega
  | orderDeleteMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderDeleteMessage.encode_length]
    omega
  | resetMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, ResetMessage.encode_length]
    omega
  | communicationControlMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, CommunicationControlMessage.encode_length]
    omega

/-- Size rule: Tag Length counts the bytes after it, so it is written from the body and checked on decode -/
def encode : Message → List UInt8 :=
  encodeFramed 1 0 encodeBody

def decode : List UInt8 → Option (Message × List UInt8) :=
  decodeFramed 1 0 decodeBody

@[simp] theorem decode_encode (message : Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramed_encodeFramed 1 0 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : Message) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramed_length]
  omega

end Message

/-- Udp Packet -/
structure UdpPacket where
  multicastGroupNumber : BitVec 8
  numberOfSystemReboots : BitVec 8
  sequenceNumber : BitVec 32
  issueCode : Alpha 12
  updateNumber : BitVec 32
  packetNumber : BitVec 8
  totalNumberOfPackets : BitVec 8
  utilityFlag : BitVec 8
  message : Bounded 1 Message
  deriving DecidableEq, Repr

namespace UdpPacket

def encode (message : UdpPacket) : List UInt8 :=
  encodeUInt 1 message.multicastGroupNumber
    ++ (encodeUInt 1 message.numberOfSystemReboots
    ++ (encodeUInt 4 message.sequenceNumber
    ++ (Alpha.encode message.issueCode
    ++ (encodeUInt 4 message.updateNumber
    ++ (encodeUInt 1 message.packetNumber
    ++ (encodeUInt 1 message.totalNumberOfPackets
    ++ (encodeUInt 1 message.utilityFlag
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.message.val.length)
    ++ (encodeMany Message.encode message.message.val)))))))))

def decode (bytes : List UInt8) : Option (UdpPacket × List UInt8) := do
  let (multicastGroupNumber, bytes) ← decodeUInt 1 bytes
  let (numberOfSystemReboots, bytes) ← decodeUInt 1 bytes
  let (sequenceNumber, bytes) ← decodeUInt 4 bytes
  let (issueCode, bytes) ← Alpha.decode 12 bytes
  let (updateNumber, bytes) ← decodeUInt 4 bytes
  let (packetNumber, bytes) ← decodeUInt 1 bytes
  let (totalNumberOfPackets, bytes) ← decodeUInt 1 bytes
  let (utilityFlag, bytes) ← decodeUInt 1 bytes
  let (messageCount, bytes) ← decodeUInt 1 bytes
  let (message_, bytes) ← decodeMany Message.decode messageCount.toNat bytes
  if fits_message : message_.length < 256 ^ 1 then
    pure ({ multicastGroupNumber, numberOfSystemReboots, sequenceNumber, issueCode, updateNumber, packetNumber, totalNumberOfPackets, utilityFlag, message := ⟨message_, fits_message⟩ }, bytes)
  else none

theorem encode_length_pos (message : UdpPacket) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, ← Nat.add_assoc]
  omega

@[simp] theorem decode_encode (message : UdpPacket) (rest : List UInt8) :
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
  rw [decodeMany_bounded 1 Message.encode Message.decode Message.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.message.length_lt]
  rfl

end UdpPacket

end Omi.JpxFseequitiesMarketbyorderFlexV11Udp
