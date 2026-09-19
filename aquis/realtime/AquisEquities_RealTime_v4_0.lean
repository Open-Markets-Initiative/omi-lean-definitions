import Omi.Wire

/-!
# Aquis Exchange Real Time Market Data Feed v4.0

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Md Flags is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Binary Mmt is a bit field set, proven as its 4 byte integer rather than bit by bit.

Note: Security Definition Flags is a bit field set, proven as its 2 byte integer rather than bit by bit.

Note: Market Flags is a bit field set, proven as its 1 byte integer rather than bit by bit.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.AquisAquisequitiesRealtimeAmdV40

/-- Order Add: 28 bytes -/
structure OrderAdd where
  securityId : BitVec 16
  side : BitVec 8
  quantity : BitVec 32
  price : BitVec 64
  orderRef : BitVec 32
  timestamp : BitVec 64
  mdFlags : BitVec 8
  deriving DecidableEq, Repr

namespace OrderAdd

def encode (message : OrderAdd) : List UInt8 :=
  encodeUIntLE 2 message.securityId
    ++ (encodeUIntLE 1 message.side
    ++ (encodeUIntLE 4 message.quantity
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.orderRef
    ++ (encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 1 message.mdFlags))))))

def decode (bytes : List UInt8) : Option (OrderAdd × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 2 bytes
  let (side, bytes) ← decodeUIntLE 1 bytes
  let (quantity, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (orderRef, bytes) ← decodeUIntLE 4 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (mdFlags, bytes) ← decodeUIntLE 1 bytes
  pure ({ securityId, side, quantity, price, orderRef, timestamp, mdFlags }, bytes)

@[simp] theorem encode_length (message : OrderAdd) : (encode message).length = 28 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : OrderAdd) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderAdd) (rest : List UInt8) :
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

end OrderAdd

/-- Order Cancel: 15 bytes -/
structure OrderCancel where
  securityId : BitVec 16
  orderRef : BitVec 32
  timestamp : BitVec 64
  mdFlags : BitVec 8
  deriving DecidableEq, Repr

namespace OrderCancel

def encode (message : OrderCancel) : List UInt8 :=
  encodeUIntLE 2 message.securityId
    ++ (encodeUIntLE 4 message.orderRef
    ++ (encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 1 message.mdFlags)))

def decode (bytes : List UInt8) : Option (OrderCancel × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 2 bytes
  let (orderRef, bytes) ← decodeUIntLE 4 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (mdFlags, bytes) ← decodeUIntLE 1 bytes
  pure ({ securityId, orderRef, timestamp, mdFlags }, bytes)

@[simp] theorem encode_length (message : OrderCancel) : (encode message).length = 15 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : OrderCancel) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderCancel) (rest : List UInt8) :
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

end OrderCancel

/-- Order Modify: 27 bytes -/
structure OrderModify where
  securityId : BitVec 16
  quantity : BitVec 32
  price : BitVec 64
  orderRef : BitVec 32
  timestamp : BitVec 64
  mdFlags : BitVec 8
  deriving DecidableEq, Repr

namespace OrderModify

def encode (message : OrderModify) : List UInt8 :=
  encodeUIntLE 2 message.securityId
    ++ (encodeUIntLE 4 message.quantity
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.orderRef
    ++ (encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 1 message.mdFlags)))))

def decode (bytes : List UInt8) : Option (OrderModify × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 2 bytes
  let (quantity, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (orderRef, bytes) ← decodeUIntLE 4 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (mdFlags, bytes) ← decodeUIntLE 1 bytes
  pure ({ securityId, quantity, price, orderRef, timestamp, mdFlags }, bytes)

@[simp] theorem encode_length (message : OrderModify) : (encode message).length = 27 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : OrderModify) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderModify) (rest : List UInt8) :
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

end OrderModify

/-- Trade: 36 bytes -/
structure Trade where
  securityId : BitVec 16
  tradeType : BitVec 8
  quantity : BitVec 32
  price : BitVec 64
  orderRef : BitVec 32
  tradeRef : BitVec 32
  timestamp : BitVec 64
  binaryMmt : BitVec 32
  mdFlags : BitVec 8
  deriving DecidableEq, Repr

namespace Trade

def encode (message : Trade) : List UInt8 :=
  encodeUIntLE 2 message.securityId
    ++ (encodeUIntLE 1 message.tradeType
    ++ (encodeUIntLE 4 message.quantity
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.orderRef
    ++ (encodeUIntLE 4 message.tradeRef
    ++ (encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 4 message.binaryMmt
    ++ (encodeUIntLE 1 message.mdFlags))))))))

def decode (bytes : List UInt8) : Option (Trade × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 2 bytes
  let (tradeType, bytes) ← decodeUIntLE 1 bytes
  let (quantity, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (orderRef, bytes) ← decodeUIntLE 4 bytes
  let (tradeRef, bytes) ← decodeUIntLE 4 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (binaryMmt, bytes) ← decodeUIntLE 4 bytes
  let (mdFlags, bytes) ← decodeUIntLE 1 bytes
  pure ({ securityId, tradeType, quantity, price, orderRef, tradeRef, timestamp, binaryMmt, mdFlags }, bytes)

@[simp] theorem encode_length (message : Trade) : (encode message).length = 36 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : Trade) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Trade) (rest : List UInt8) :
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

end Trade

/-- Trade Bust Message: 30 bytes -/
structure TradeBustMessage where
  securityId : BitVec 16
  quantity : BitVec 32
  price : BitVec 64
  tradeRef : BitVec 32
  timestamp : BitVec 64
  binaryMmt : BitVec 32
  deriving DecidableEq, Repr

namespace TradeBustMessage

def encode (message : TradeBustMessage) : List UInt8 :=
  encodeUIntLE 2 message.securityId
    ++ (encodeUIntLE 4 message.quantity
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.tradeRef
    ++ (encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 4 message.binaryMmt)))))

def decode (bytes : List UInt8) : Option (TradeBustMessage × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 2 bytes
  let (quantity, bytes) ← decodeUIntLE 4 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (tradeRef, bytes) ← decodeUIntLE 4 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (binaryMmt, bytes) ← decodeUIntLE 4 bytes
  pure ({ securityId, quantity, price, tradeRef, timestamp, binaryMmt }, bytes)

@[simp] theorem encode_length (message : TradeBustMessage) : (encode message).length = 30 := by
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

/-- Security Definition Message: 59 bytes -/
structure SecurityDefinitionMessage where
  securityId : BitVec 16
  umtf : Alpha 6
  isin : Alpha 12
  currency : Alpha 3
  mic : Alpha 4
  tickTableId : BitVec 8
  securityDefinitionFlags : BitVec 16
  reserved : Alpha 20
  lotSize : BitVec 64
  lotSizeDecimal : BitVec 8
  deriving DecidableEq, Repr

namespace SecurityDefinitionMessage

def encode (message : SecurityDefinitionMessage) : List UInt8 :=
  encodeUIntLE 2 message.securityId
    ++ (Alpha.encode message.umtf
    ++ (Alpha.encode message.isin
    ++ (Alpha.encode message.currency
    ++ (Alpha.encode message.mic
    ++ (encodeUIntLE 1 message.tickTableId
    ++ (encodeUIntLE 2 message.securityDefinitionFlags
    ++ (Alpha.encode message.reserved
    ++ (encodeUIntLE 8 message.lotSize
    ++ (encodeUIntLE 1 message.lotSizeDecimal)))))))))

def decode (bytes : List UInt8) : Option (SecurityDefinitionMessage × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 2 bytes
  let (umtf, bytes) ← Alpha.decode 6 bytes
  let (isin, bytes) ← Alpha.decode 12 bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  let (mic, bytes) ← Alpha.decode 4 bytes
  let (tickTableId, bytes) ← decodeUIntLE 1 bytes
  let (securityDefinitionFlags, bytes) ← decodeUIntLE 2 bytes
  let (reserved, bytes) ← Alpha.decode 20 bytes
  let (lotSize, bytes) ← decodeUIntLE 8 bytes
  let (lotSizeDecimal, bytes) ← decodeUIntLE 1 bytes
  pure ({ securityId, umtf, isin, currency, mic, tickTableId, securityDefinitionFlags, reserved, lotSize, lotSizeDecimal }, bytes)

@[simp] theorem encode_length (message : SecurityDefinitionMessage) : (encode message).length = 59 := by
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SecurityDefinitionMessage

/-- Security Status Message: 13 bytes -/
structure SecurityStatusMessage where
  securityId : BitVec 16
  tradingStatus : BitVec 8
  marketFlags : BitVec 8
  timestamp : BitVec 64
  tradingPhase : BitVec 8
  deriving DecidableEq, Repr

namespace SecurityStatusMessage

def encode (message : SecurityStatusMessage) : List UInt8 :=
  encodeUIntLE 2 message.securityId
    ++ (encodeUIntLE 1 message.tradingStatus
    ++ (encodeUIntLE 1 message.marketFlags
    ++ (encodeUIntLE 8 message.timestamp
    ++ (encodeUIntLE 1 message.tradingPhase))))

def decode (bytes : List UInt8) : Option (SecurityStatusMessage × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 2 bytes
  let (tradingStatus, bytes) ← decodeUIntLE 1 bytes
  let (marketFlags, bytes) ← decodeUIntLE 1 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  let (tradingPhase, bytes) ← decodeUIntLE 1 bytes
  pure ({ securityId, tradingStatus, marketFlags, timestamp, tradingPhase }, bytes)

@[simp] theorem encode_length (message : SecurityStatusMessage) : (encode message).length = 13 := by
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end SecurityStatusMessage

/-- Ao D Update Message: 22 bytes -/
structure AoDUpdateMessage where
  securityId : BitVec 16
  indicativePrice : BitVec 64
  matchVol : BitVec 32
  timestamp : BitVec 64
  deriving DecidableEq, Repr

namespace AoDUpdateMessage

def encode (message : AoDUpdateMessage) : List UInt8 :=
  encodeUIntLE 2 message.securityId
    ++ (encodeUIntLE 8 message.indicativePrice
    ++ (encodeUIntLE 4 message.matchVol
    ++ (encodeUIntLE 8 message.timestamp)))

def decode (bytes : List UInt8) : Option (AoDUpdateMessage × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 2 bytes
  let (indicativePrice, bytes) ← decodeUIntLE 8 bytes
  let (matchVol, bytes) ← decodeUIntLE 4 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  pure ({ securityId, indicativePrice, matchVol, timestamp }, bytes)

@[simp] theorem encode_length (message : AoDUpdateMessage) : (encode message).length = 22 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : AoDUpdateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AoDUpdateMessage) (rest : List UInt8) :
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

end AoDUpdateMessage

/-- Ma C Update Message: 26 bytes -/
structure MaCUpdateMessage where
  securityId : BitVec 16
  indicativePrice : BitVec 64
  closingBuyQty : BitVec 32
  closingSellQty : BitVec 32
  timestamp : BitVec 64
  deriving DecidableEq, Repr

namespace MaCUpdateMessage

def encode (message : MaCUpdateMessage) : List UInt8 :=
  encodeUIntLE 2 message.securityId
    ++ (encodeUIntLE 8 message.indicativePrice
    ++ (encodeUIntLE 4 message.closingBuyQty
    ++ (encodeUIntLE 4 message.closingSellQty
    ++ (encodeUIntLE 8 message.timestamp))))

def decode (bytes : List UInt8) : Option (MaCUpdateMessage × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 2 bytes
  let (indicativePrice, bytes) ← decodeUIntLE 8 bytes
  let (closingBuyQty, bytes) ← decodeUIntLE 4 bytes
  let (closingSellQty, bytes) ← decodeUIntLE 4 bytes
  let (timestamp, bytes) ← decodeUIntLE 8 bytes
  pure ({ securityId, indicativePrice, closingBuyQty, closingSellQty, timestamp }, bytes)

@[simp] theorem encode_length (message : MaCUpdateMessage) : (encode message).length = 26 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : MaCUpdateMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MaCUpdateMessage) (rest : List UInt8) :
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

end MaCUpdateMessage

/-- Any Payload, selected by Msg Type -/
inductive Payload where
  | orderAdd (message : OrderAdd) -- 2
  | orderCancel (message : OrderCancel) -- 3
  | orderModify (message : OrderModify) -- 4
  | trade (message : Trade) -- 5
  | tradeBustMessage (message : TradeBustMessage) -- 6
  | tickTableDataMessage (message : TickTableDataMessage) -- 7
  | securityDefinitionMessage (message : SecurityDefinitionMessage) -- 8
  | securityStatusMessage (message : SecurityStatusMessage) -- 9
  | aoDUpdateMessage (message : AoDUpdateMessage) -- 17
  | maCUpdateMessage (message : MaCUpdateMessage) -- 16
  deriving DecidableEq, Repr

namespace Payload

/-- The Msg Type each message is sent under -/
def tag : Payload → BitVec 8
  | .orderAdd _ => 2
  | .orderCancel _ => 3
  | .orderModify _ => 4
  | .trade _ => 5
  | .tradeBustMessage _ => 6
  | .tickTableDataMessage _ => 7
  | .securityDefinitionMessage _ => 8
  | .securityStatusMessage _ => 9
  | .aoDUpdateMessage _ => 17
  | .maCUpdateMessage _ => 16

def encode : Payload → List UInt8
  | .orderAdd message => OrderAdd.encode message
  | .orderCancel message => OrderCancel.encode message
  | .orderModify message => OrderModify.encode message
  | .trade message => Trade.encode message
  | .tradeBustMessage message => TradeBustMessage.encode message
  | .tickTableDataMessage message => TickTableDataMessage.encode message
  | .securityDefinitionMessage message => SecurityDefinitionMessage.encode message
  | .securityStatusMessage message => SecurityStatusMessage.encode message
  | .aoDUpdateMessage message => AoDUpdateMessage.encode message
  | .maCUpdateMessage message => MaCUpdateMessage.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : Payload) : (encode message).length ≤ 59 := by
  cases message with
  | orderAdd inner =>
    simp only [encode, OrderAdd.encode_length]
    omega
  | orderCancel inner =>
    simp only [encode, OrderCancel.encode_length]
    omega
  | orderModify inner =>
    simp only [encode, OrderModify.encode_length]
    omega
  | trade inner =>
    simp only [encode, Trade.encode_length]
    omega
  | tradeBustMessage inner =>
    simp only [encode, TradeBustMessage.encode_length]
    omega
  | tickTableDataMessage inner =>
    simp only [encode, TickTableDataMessage.encode_length]
    omega
  | securityDefinitionMessage inner =>
    simp only [encode, SecurityDefinitionMessage.encode_length]
    omega
  | securityStatusMessage inner =>
    simp only [encode, SecurityStatusMessage.encode_length]
    omega
  | aoDUpdateMessage inner =>
    simp only [encode, AoDUpdateMessage.encode_length]
    omega
  | maCUpdateMessage inner =>
    simp only [encode, MaCUpdateMessage.encode_length]
    omega

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 2 then (OrderAdd.decode bytes).map fun (message, rest) => (.orderAdd message, rest)
  else if tag = 3 then (OrderCancel.decode bytes).map fun (message, rest) => (.orderCancel message, rest)
  else if tag = 4 then (OrderModify.decode bytes).map fun (message, rest) => (.orderModify message, rest)
  else if tag = 5 then (Trade.decode bytes).map fun (message, rest) => (.trade message, rest)
  else if tag = 6 then (TradeBustMessage.decode bytes).map fun (message, rest) => (.tradeBustMessage message, rest)
  else if tag = 7 then (TickTableDataMessage.decode bytes).map fun (message, rest) => (.tickTableDataMessage message, rest)
  else if tag = 8 then (SecurityDefinitionMessage.decode bytes).map fun (message, rest) => (.securityDefinitionMessage message, rest)
  else if tag = 9 then (SecurityStatusMessage.decode bytes).map fun (message, rest) => (.securityStatusMessage message, rest)
  else if tag = 17 then (AoDUpdateMessage.decode bytes).map fun (message, rest) => (.aoDUpdateMessage message, rest)
  else if tag = 16 then (MaCUpdateMessage.decode bytes).map fun (message, rest) => (.maCUpdateMessage message, rest)
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
  | orderAdd inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderAdd.encode_length]
    omega
  | orderCancel inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderCancel.encode_length]
    omega
  | orderModify inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, OrderModify.encode_length]
    omega
  | trade inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, Trade.encode_length]
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
  | aoDUpdateMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, AoDUpdateMessage.encode_length]
    omega
  | maCUpdateMessage inner =>
    simp only [Payload.encode, List.length_append, encodeUInt_length, MaCUpdateMessage.encode_length]
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

end Omi.AquisAquisequitiesRealtimeAmdV40
