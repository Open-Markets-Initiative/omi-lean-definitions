import Omi.Wire

/-!
# A2X Markets Real Time Market Data Feed v1.3.2

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Security Flags is a bit field set, proven as its 2 byte integer rather than bit by bit.

Note: Market Flags is a bit field set, proven as its 1 byte integer rather than bit by bit.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.A2xA2xequitiesRtmdfAmdV132

/-- Heartbeat Message: 0 bytes -/
structure HeartbeatMessage where
  deriving DecidableEq, Repr

namespace HeartbeatMessage

def encode (_ : HeartbeatMessage) : List UInt8 :=
  []

def decode (bytes : List UInt8) : Option (HeartbeatMessage × List UInt8) :=
  some (⟨⟩, bytes)

@[simp] theorem encode_length (message : HeartbeatMessage) : (encode message).length = 0 := by
  simp [encode]

@[simp] theorem decode_encode (message : HeartbeatMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  simp [decode, encode]

end HeartbeatMessage

/-- Order Add Message: 27 bytes -/
structure OrderAddMessage where
  securityId : BitVec 16
  side : BitVec 8
  quantity : BitVec 32
  price : BitVec 64
  orderRef : BitVec 32
  timestamp : BitVec 64
  deriving DecidableEq, Repr

namespace OrderAddMessage

def encode (message : OrderAddMessage) : List UInt8 :=
  encodeUIntLE 2 message.securityId
    ++ (encodeUIntLE 1 message.side
    ++ (encodeUIntLE 4 message.quantity
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.orderRef
    ++ (encodeUIntLE 8 message.timestamp)))))

def decode (bytes : List UInt8) : Option (OrderAddMessage × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 2 bytes
  let (side, bytes) ← decodeUIntLE 1 bytes
  let (quantity, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (orderRef, bytes) ← decodeUIntLE 4 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  pure ({ securityId, side, quantity, price, orderRef, timestamp }, bytes)

@[simp] theorem encode_length (message : OrderAddMessage) : (encode message).length = 27 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : OrderAddMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderAddMessage) (rest : List UInt8) :
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

end OrderAddMessage

/-- Order Cancel Message: 14 bytes -/
structure OrderCancelMessage where
  securityId : BitVec 16
  orderRef : BitVec 32
  timestamp : BitVec 64
  deriving DecidableEq, Repr

namespace OrderCancelMessage

def encode (message : OrderCancelMessage) : List UInt8 :=
  encodeUIntLE 2 message.securityId
    ++ (encodeUIntLE 4 message.orderRef
    ++ (encodeUIntLE 8 message.timestamp))

def decode (bytes : List UInt8) : Option (OrderCancelMessage × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 2 bytes
  let (orderRef, bytes) ← decodeUIntLE 4 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  pure ({ securityId, orderRef, timestamp }, bytes)

@[simp] theorem encode_length (message : OrderCancelMessage) : (encode message).length = 14 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : OrderCancelMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderCancelMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end OrderCancelMessage

/-- Order Modify Message: 26 bytes -/
structure OrderModifyMessage where
  securityId : BitVec 16
  quantity : BitVec 32
  price : BitVec 64
  orderRef : BitVec 32
  timestamp : BitVec 64
  deriving DecidableEq, Repr

namespace OrderModifyMessage

def encode (message : OrderModifyMessage) : List UInt8 :=
  encodeUIntLE 2 message.securityId
    ++ (encodeUIntLE 4 message.quantity
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.orderRef
    ++ (encodeUIntLE 8 message.timestamp))))

def decode (bytes : List UInt8) : Option (OrderModifyMessage × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 2 bytes
  let (quantity, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (orderRef, bytes) ← decodeUIntLE 4 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  pure ({ securityId, quantity, price, orderRef, timestamp }, bytes)

@[simp] theorem encode_length (message : OrderModifyMessage) : (encode message).length = 26 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : OrderModifyMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderModifyMessage) (rest : List UInt8) :
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

end OrderModifyMessage

/-- Trade Message: 31 bytes -/
structure TradeMessage where
  securityId : BitVec 16
  tradeType : BitVec 8
  quantity : BitVec 32
  price : BitVec 64
  orderRef : BitVec 32
  tradeRef : BitVec 32
  timestamp : BitVec 64
  deriving DecidableEq, Repr

namespace TradeMessage

def encode (message : TradeMessage) : List UInt8 :=
  encodeUIntLE 2 message.securityId
    ++ (encodeUIntLE 1 message.tradeType
    ++ (encodeUIntLE 4 message.quantity
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.orderRef
    ++ (encodeUIntLE 4 message.tradeRef
    ++ (encodeUIntLE 8 message.timestamp))))))

def decode (bytes : List UInt8) : Option (TradeMessage × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 2 bytes
  let (tradeType, bytes) ← decodeUIntLE 1 bytes
  let (quantity, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (orderRef, bytes) ← decodeUIntLE 4 bytes
  let (tradeRef, bytes) ← decodeUIntLE 4 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  pure ({ securityId, tradeType, quantity, price, orderRef, tradeRef, timestamp }, bytes)

@[simp] theorem encode_length (message : TradeMessage) : (encode message).length = 31 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TradeMessage

/-- Trade Bust Message: 26 bytes -/
structure TradeBustMessage where
  securityId : BitVec 16
  quantity : BitVec 32
  price : BitVec 64
  tradeRef : BitVec 32
  timestamp : BitVec 64
  deriving DecidableEq, Repr

namespace TradeBustMessage

def encode (message : TradeBustMessage) : List UInt8 :=
  encodeUIntLE 2 message.securityId
    ++ (encodeUIntLE 4 message.quantity
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.tradeRef
    ++ (encodeUIntLE 8 message.timestamp))))

def decode (bytes : List UInt8) : Option (TradeBustMessage × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 2 bytes
  let (quantity, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (tradeRef, bytes) ← decodeUIntLE 4 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  pure ({ securityId, quantity, price, tradeRef, timestamp }, bytes)

@[simp] theorem encode_length (message : TradeBustMessage) : (encode message).length = 26 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : TradeBustMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeBustMessage) (rest : List UInt8) :
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

end TradeBustMessage

/-- Tick Table Data Message: 27 bytes -/
structure TickTableDataMessage where
  tickTableId : BitVec 8
  name : Alpha 10
  threshold : BitVec 64
  tickSize : BitVec 64
  deriving DecidableEq, Repr

namespace TickTableDataMessage

def encode (message : TickTableDataMessage) : List UInt8 :=
  encodeUIntLE 1 message.tickTableId
    ++ (Alpha.encode message.name
    ++ (encodeUIntLE 8 message.threshold
    ++ (encodeUIntLE 8 message.tickSize)))

def decode (bytes : List UInt8) : Option (TickTableDataMessage × List UInt8) := do
  let (tickTableId, bytes) ← decodeUIntLE 1 bytes
  let (name, bytes) ← Alpha.decode 10 bytes
  let (threshold, bytes) ← decodeUIntLE 8 bytes
  let (tickSize, bytes) ← decodeUIntLE 8 bytes
  pure ({ tickTableId, name, threshold, tickSize }, bytes)

@[simp] theorem encode_length (message : TickTableDataMessage) : (encode message).length = 27 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : TickTableDataMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TickTableDataMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TickTableDataMessage

/-- Security Definition Message: 30 bytes -/
structure SecurityDefinitionMessage where
  securityId : BitVec 16
  umtf : Alpha 6
  isin : Alpha 12
  currency : Alpha 3
  mic : Alpha 4
  tickTableId : BitVec 8
  securityFlags : BitVec 16
  deriving DecidableEq, Repr

namespace SecurityDefinitionMessage

def encode (message : SecurityDefinitionMessage) : List UInt8 :=
  encodeUIntLE 2 message.securityId
    ++ (Alpha.encode message.umtf
    ++ (Alpha.encode message.isin
    ++ (Alpha.encode message.currency
    ++ (Alpha.encode message.mic
    ++ (encodeUIntLE 1 message.tickTableId
    ++ (encodeUIntLE 2 message.securityFlags))))))

def decode (bytes : List UInt8) : Option (SecurityDefinitionMessage × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 2 bytes
  let (umtf, bytes) ← Alpha.decode 6 bytes
  let (isin, bytes) ← Alpha.decode 12 bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  let (mic, bytes) ← Alpha.decode 4 bytes
  let (tickTableId, bytes) ← decodeUIntLE 1 bytes
  let (securityFlags, bytes) ← decodeUIntLE 2 bytes
  pure ({ securityId, umtf, isin, currency, mic, tickTableId, securityFlags }, bytes)

@[simp] theorem encode_length (message : SecurityDefinitionMessage) : (encode message).length = 30 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : SecurityDefinitionMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecurityDefinitionMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SecurityDefinitionMessage

/-- Security Status Message: 12 bytes -/
structure SecurityStatusMessage where
  securityId : BitVec 16
  tradingStatus : BitVec 8
  marketFlags : BitVec 8
  timestamp : BitVec 64
  deriving DecidableEq, Repr

namespace SecurityStatusMessage

def encode (message : SecurityStatusMessage) : List UInt8 :=
  encodeUIntLE 2 message.securityId
    ++ (encodeUIntLE 1 message.tradingStatus
    ++ (encodeUIntLE 1 message.marketFlags
    ++ (encodeUIntLE 8 message.timestamp)))

def decode (bytes : List UInt8) : Option (SecurityStatusMessage × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 2 bytes
  let (tradingStatus, bytes) ← decodeUIntLE 1 bytes
  let (marketFlags, bytes) ← decodeUIntLE 1 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  pure ({ securityId, tradingStatus, marketFlags, timestamp }, bytes)

@[simp] theorem encode_length (message : SecurityStatusMessage) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : SecurityStatusMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecurityStatusMessage) (rest : List UInt8) :
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

end SecurityStatusMessage

/-- Auction On Demand Message: 22 bytes -/
structure AuctionOnDemandMessage where
  securityId : BitVec 16
  indicativePrice : BitVec 64
  matchVol : BitVec 32
  timestamp : BitVec 64
  deriving DecidableEq, Repr

namespace AuctionOnDemandMessage

def encode (message : AuctionOnDemandMessage) : List UInt8 :=
  encodeUIntLE 2 message.securityId
    ++ (encodeUIntLE 8 message.indicativePrice
    ++ (encodeUIntLE 4 message.matchVol
    ++ (encodeUIntLE 8 message.timestamp)))

def decode (bytes : List UInt8) : Option (AuctionOnDemandMessage × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 2 bytes
  let (indicativePrice, bytes) ← decodeUIntLE 8 bytes
  let (matchVol, bytes) ← decodeUIntLE 4 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  pure ({ securityId, indicativePrice, matchVol, timestamp }, bytes)

@[simp] theorem encode_length (message : AuctionOnDemandMessage) : (encode message).length = 22 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : AuctionOnDemandMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AuctionOnDemandMessage) (rest : List UInt8) :
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

end AuctionOnDemandMessage

/-- Market At Close: 26 bytes -/
structure MarketAtClose where
  securityId : BitVec 16
  indicativePrice : BitVec 64
  closingBuyQty : BitVec 32
  closingSellQty : BitVec 32
  timestamp : BitVec 64
  deriving DecidableEq, Repr

namespace MarketAtClose

def encode (message : MarketAtClose) : List UInt8 :=
  encodeUIntLE 2 message.securityId
    ++ (encodeUIntLE 8 message.indicativePrice
    ++ (encodeUIntLE 4 message.closingBuyQty
    ++ (encodeUIntLE 4 message.closingSellQty
    ++ (encodeUIntLE 8 message.timestamp))))

def decode (bytes : List UInt8) : Option (MarketAtClose × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 2 bytes
  let (indicativePrice, bytes) ← decodeUIntLE 8 bytes
  let (closingBuyQty, bytes) ← decodeUIntLE 4 bytes
  let (closingSellQty, bytes) ← decodeUIntLE 4 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  pure ({ securityId, indicativePrice, closingBuyQty, closingSellQty, timestamp }, bytes)

@[simp] theorem encode_length (message : MarketAtClose) : (encode message).length = 26 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : MarketAtClose) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MarketAtClose) (rest : List UInt8) :
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

end MarketAtClose

/-- Any Payload, selected by Msg Type -/
inductive Payload where
  | heartbeatMessage (message : HeartbeatMessage) -- 1
  | orderAddMessage (message : OrderAddMessage) -- 2
  | orderCancelMessage (message : OrderCancelMessage) -- 3
  | orderModifyMessage (message : OrderModifyMessage) -- 4
  | tradeMessage (message : TradeMessage) -- 5
  | tradeBustMessage (message : TradeBustMessage) -- 6
  | tickTableDataMessage (message : TickTableDataMessage) -- 7
  | securityDefinitionMessage (message : SecurityDefinitionMessage) -- 8
  | securityStatusMessage (message : SecurityStatusMessage) -- 9
  | auctionOnDemandMessage (message : AuctionOnDemandMessage) -- 17
  | marketAtClose (message : MarketAtClose) -- 16
  deriving DecidableEq, Repr

namespace Payload

/-- The Msg Type each message is sent under -/
def tag : Payload → BitVec 8
  | .heartbeatMessage _ => 1
  | .orderAddMessage _ => 2
  | .orderCancelMessage _ => 3
  | .orderModifyMessage _ => 4
  | .tradeMessage _ => 5
  | .tradeBustMessage _ => 6
  | .tickTableDataMessage _ => 7
  | .securityDefinitionMessage _ => 8
  | .securityStatusMessage _ => 9
  | .auctionOnDemandMessage _ => 17
  | .marketAtClose _ => 16

def encode : Payload → List UInt8
  | .heartbeatMessage message => HeartbeatMessage.encode message
  | .orderAddMessage message => OrderAddMessage.encode message
  | .orderCancelMessage message => OrderCancelMessage.encode message
  | .orderModifyMessage message => OrderModifyMessage.encode message
  | .tradeMessage message => TradeMessage.encode message
  | .tradeBustMessage message => TradeBustMessage.encode message
  | .tickTableDataMessage message => TickTableDataMessage.encode message
  | .securityDefinitionMessage message => SecurityDefinitionMessage.encode message
  | .securityStatusMessage message => SecurityStatusMessage.encode message
  | .auctionOnDemandMessage message => AuctionOnDemandMessage.encode message
  | .marketAtClose message => MarketAtClose.encode message

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 1 then (HeartbeatMessage.decode bytes).map fun (message, rest) => (.heartbeatMessage message, rest)
  else if tag = 2 then (OrderAddMessage.decode bytes).map fun (message, rest) => (.orderAddMessage message, rest)
  else if tag = 3 then (OrderCancelMessage.decode bytes).map fun (message, rest) => (.orderCancelMessage message, rest)
  else if tag = 4 then (OrderModifyMessage.decode bytes).map fun (message, rest) => (.orderModifyMessage message, rest)
  else if tag = 5 then (TradeMessage.decode bytes).map fun (message, rest) => (.tradeMessage message, rest)
  else if tag = 6 then (TradeBustMessage.decode bytes).map fun (message, rest) => (.tradeBustMessage message, rest)
  else if tag = 7 then (TickTableDataMessage.decode bytes).map fun (message, rest) => (.tickTableDataMessage message, rest)
  else if tag = 8 then (SecurityDefinitionMessage.decode bytes).map fun (message, rest) => (.securityDefinitionMessage message, rest)
  else if tag = 9 then (SecurityStatusMessage.decode bytes).map fun (message, rest) => (.securityStatusMessage message, rest)
  else if tag = 17 then (AuctionOnDemandMessage.decode bytes).map fun (message, rest) => (.auctionOnDemandMessage message, rest)
  else if tag = 16 then (MarketAtClose.decode bytes).map fun (message, rest) => (.marketAtClose message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Message -/
structure Message where
  seqNo : BitVec 32
  payload : Payload
  deriving DecidableEq, Repr

namespace Message

def encodeBody (message : Message) : List UInt8 :=
  encodeUInt 4 message.seqNo
    ++ (Payload.encode message.payload)

def decodeBody (msgType : BitVec 8) (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (seqNo, bytes) ← decodeUInt 4 bytes
  let (payload, bytes) ← Payload.decode msgType bytes
  pure ({ seqNo, payload }, bytes)

theorem decodeBody_encodeBody (message : Message) (rest : List UInt8) :
    decodeBody (Payload.tag message.payload) (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Payload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : Message) : (encodeBody message).length + 2 < 256 ^ 1 := by
  unfold encodeBody
  cases message.payload with
  | heartbeatMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, HeartbeatMessage.encode_length]
    omega
  | orderAddMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderAddMessage.encode_length]
    omega
  | orderCancelMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderCancelMessage.encode_length]
    omega
  | orderModifyMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderModifyMessage.encode_length]
    omega
  | tradeMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TradeMessage.encode_length]
    omega
  | tradeBustMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TradeBustMessage.encode_length]
    omega
  | tickTableDataMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, TickTableDataMessage.encode_length]
    omega
  | securityDefinitionMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SecurityDefinitionMessage.encode_length]
    omega
  | securityStatusMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, SecurityStatusMessage.encode_length]
    omega
  | auctionOnDemandMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, AuctionOnDemandMessage.encode_length]
    omega
  | marketAtClose inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, MarketAtClose.encode_length]
    omega

/-- Size rule: Msg Length counts the bytes after it plus 2, so it is written from the body and checked on decode; Msg Type is read ahead of it -/
def encode (message : Message) : List UInt8 :=
  encodeUInt 1 (Payload.tag message.payload)
    ++ (encodeFramed 1 2 encodeBody message)

def decode (bytes : List UInt8) : Option (Message × List UInt8) := do
  let (msgType, bytes) ← decodeUInt 1 bytes
  decodeFramed 1 2 (decodeBody msgType) bytes

@[simp] theorem decode_encode (message : Message) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  exact decodeFramed_encodeFramed 1 2 encodeBody (decodeBody (Payload.tag message.payload)) message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

theorem encode_length_pos (message : Message) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append, encodeFramed_length]
  omega

end Message

/-- Packet -/
structure Packet where
  message : Bounded 1 Message
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeUInt 1 (BitVec.ofNat (8 * 1) message.message.val.length)
    ++ (encodeMany Message.encode message.message.val)

def decode (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (messageCount, bytes) ← decodeUInt 1 bytes
  let (message_, bytes) ← decodeMany Message.decode messageCount.toNat bytes
  if fits_message : message_.length < 256 ^ 1 then
    pure ({ message := ⟨message_, fits_message⟩ }, bytes)
  else none

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUInt_length, List.length_append]
  omega

@[simp] theorem decode_encode (message : Packet) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 Message.encode Message.decode Message.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.message.length_lt]
  rfl

end Packet

end Omi.A2xA2xequitiesRtmdfAmdV132
