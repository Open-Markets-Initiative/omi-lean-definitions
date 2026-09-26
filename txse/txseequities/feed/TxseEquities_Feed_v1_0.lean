import Omi.Wire
import Std.Tactic.BVDecide

/-!
# Texas Stock Exchange FEED Full-Depth Market Data v1.0

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Trading Session Status Presence Bits is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Define Symbol Bit Fields is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Symbol Status Presence Bits is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Order Bit Fields is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Execution Bit Fields is a bit field set, proven as its 1 byte integer rather than bit by bit.

Note: Udp Sequenced Message's Message Length is written from its body but not checked on decode, since the body has no bound the prefix must fit; the body is read by its content.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.TxseTxseequitiesFeedRakeV10

/-- Trading Session Status Message -/
structure TradingSessionStatusMessage where
  tradingSessionStatusPresenceBits : Masked 8 3
  transactTime : BitVec 64
  marketHoursState : BitVec 8
  sessionTradingState : BitVec 8
  tradingSessionStatusOperationalHaltReason : Option (BitVec 8)
  tradingSessionStatusRegulatoryHaltReason : Option (BitVec 8)
  deriving DecidableEq, Repr

namespace TradingSessionStatusMessage

def encode (message : TradingSessionStatusMessage) : List UInt8 :=
  encodeUIntLE 1 (message.tradingSessionStatusPresenceBits.val ||| presence (n := 8) 1 message.tradingSessionStatusOperationalHaltReason.isSome ||| presence (n := 8) 2 message.tradingSessionStatusRegulatoryHaltReason.isSome)
    ++ (encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 1 message.marketHoursState
    ++ (encodeUIntLE 1 message.sessionTradingState
    ++ (encodeOptional (encodeUIntLE 1) message.tradingSessionStatusOperationalHaltReason
    ++ (encodeOptional (encodeUIntLE 1) message.tradingSessionStatusRegulatoryHaltReason)))))

def decode (bytes : List UInt8) : Option (TradingSessionStatusMessage × List UInt8) := do
  let (tradingSessionStatusPresenceBits_, bytes) ← decodeUIntLE 1 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (marketHoursState, bytes) ← decodeUIntLE 1 bytes
  let (sessionTradingState, bytes) ← decodeUIntLE 1 bytes
  let (tradingSessionStatusOperationalHaltReason, bytes) ← decodeOptional (decodeUIntLE 1) (tradingSessionStatusPresenceBits_ &&& 1 != 0) bytes
  let (tradingSessionStatusRegulatoryHaltReason, bytes) ← decodeOptional (decodeUIntLE 1) (tradingSessionStatusPresenceBits_ &&& 2 != 0) bytes
  if fits_tradingSessionStatusPresenceBits : (tradingSessionStatusPresenceBits_ &&& 252) &&& 3 = 0 then
    pure ({ tradingSessionStatusPresenceBits := ⟨tradingSessionStatusPresenceBits_ &&& 252, fits_tradingSessionStatusPresenceBits⟩, transactTime, marketHoursState, sessionTradingState, tradingSessionStatusOperationalHaltReason, tradingSessionStatusRegulatoryHaltReason }, bytes)
  else none

theorem encode_length_pos (message : TradingSessionStatusMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

@[simp] theorem decode_encode (message : TradingSessionStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  have selected_tradingSessionStatusOperationalHaltReason : ((message.tradingSessionStatusPresenceBits.val ||| presence (n := 8) 1 message.tradingSessionStatusOperationalHaltReason.isSome ||| presence (n := 8) 2 message.tradingSessionStatusRegulatoryHaltReason.isSome) &&& 1 != 0) = message.tradingSessionStatusOperationalHaltReason.isSome := by
    have clear := message.tradingSessionStatusPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_tradingSessionStatusRegulatoryHaltReason : ((message.tradingSessionStatusPresenceBits.val ||| presence (n := 8) 1 message.tradingSessionStatusOperationalHaltReason.isSome ||| presence (n := 8) 2 message.tradingSessionStatusRegulatoryHaltReason.isSome) &&& 2 != 0) = message.tradingSessionStatusRegulatoryHaltReason.isSome := by
    have clear := message.tradingSessionStatusPresenceBits.property
    simp only [presence]
    bv_decide
  have carried_tradingSessionStatusPresenceBits : (message.tradingSessionStatusPresenceBits.val ||| presence (n := 8) 1 message.tradingSessionStatusOperationalHaltReason.isSome ||| presence (n := 8) 2 message.tradingSessionStatusRegulatoryHaltReason.isSome) &&& 252 = message.tradingSessionStatusPresenceBits.val := by
    have clear := message.tradingSessionStatusPresenceBits.property
    simp only [presence]
    bv_decide
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [selected_tradingSessionStatusOperationalHaltReason]
  rw [List.append_assoc, decodeOptional_encodeOptional (encodeUIntLE 1) (decodeUIntLE 1) (decodeUIntLE_encodeUIntLE 1), some_bind]
  dsimp only
  rw [selected_tradingSessionStatusRegulatoryHaltReason]
  rw [decodeOptional_encodeOptional (encodeUIntLE 1) (decodeUIntLE 1) (decodeUIntLE_encodeUIntLE 1), some_bind]
  dsimp only
  rw [dite_eq_left (by rw [carried_tradingSessionStatusPresenceBits]; exact message.tradingSessionStatusPresenceBits.property)]
  simp only [carried_tradingSessionStatusPresenceBits]
  rfl

end TradingSessionStatusMessage

/-- Define Symbol Message: 33 bytes -/
structure DefineSymbolMessage where
  transactTime : BitVec 64
  symbolId : BitVec 16
  symbol : Alpha 8
  suffix : Alpha 8
  matchingEngineId : BitVec 8
  defineSymbolBitFields : BitVec 8
  lotSize : BitVec 32
  listingMarket : BitVec 8
  deriving DecidableEq, Repr

namespace DefineSymbolMessage

def encode (message : DefineSymbolMessage) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 2 message.symbolId
    ++ (Alpha.encode message.symbol
    ++ (Alpha.encode message.suffix
    ++ (encodeUIntLE 1 message.matchingEngineId
    ++ (encodeUIntLE 1 message.defineSymbolBitFields
    ++ (encodeUIntLE 4 message.lotSize
    ++ (encodeUIntLE 1 message.listingMarket)))))))

def decode (bytes : List UInt8) : Option (DefineSymbolMessage × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (symbolId, bytes) ← decodeUIntLE 2 bytes
  let (symbol, bytes) ← Alpha.decode 8 bytes
  let (suffix, bytes) ← Alpha.decode 8 bytes
  let (matchingEngineId, bytes) ← decodeUIntLE 1 bytes
  let (defineSymbolBitFields, bytes) ← decodeUIntLE 1 bytes
  let (lotSize, bytes) ← decodeUIntLE 4 bytes
  let (listingMarket, bytes) ← decodeUIntLE 1 bytes
  pure ({ transactTime, symbolId, symbol, suffix, matchingEngineId, defineSymbolBitFields, lotSize, listingMarket }, bytes)

@[simp] theorem encode_length (message : DefineSymbolMessage) : (encode message).length = 33 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : DefineSymbolMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DefineSymbolMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end DefineSymbolMessage

/-- Symbol Status Message -/
structure SymbolStatusMessage where
  symbolStatusPresenceBits : Masked 8 3
  transactTime : BitVec 64
  symbolId : BitVec 16
  symbolTradingState : BitVec 8
  shortSaleRestrictionState : BitVec 8
  symbolStatusOperationalHaltReason : Option (BitVec 8)
  symbolStatusRegulatoryHaltReason : Option (BitVec 8)
  deriving DecidableEq, Repr

namespace SymbolStatusMessage

def encode (message : SymbolStatusMessage) : List UInt8 :=
  encodeUIntLE 1 (message.symbolStatusPresenceBits.val ||| presence (n := 8) 1 message.symbolStatusOperationalHaltReason.isSome ||| presence (n := 8) 2 message.symbolStatusRegulatoryHaltReason.isSome)
    ++ (encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 2 message.symbolId
    ++ (encodeUIntLE 1 message.symbolTradingState
    ++ (encodeUIntLE 1 message.shortSaleRestrictionState
    ++ (encodeOptional (encodeUIntLE 1) message.symbolStatusOperationalHaltReason
    ++ (encodeOptional (encodeUIntLE 1) message.symbolStatusRegulatoryHaltReason))))))

def decode (bytes : List UInt8) : Option (SymbolStatusMessage × List UInt8) := do
  let (symbolStatusPresenceBits_, bytes) ← decodeUIntLE 1 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (symbolId, bytes) ← decodeUIntLE 2 bytes
  let (symbolTradingState, bytes) ← decodeUIntLE 1 bytes
  let (shortSaleRestrictionState, bytes) ← decodeUIntLE 1 bytes
  let (symbolStatusOperationalHaltReason, bytes) ← decodeOptional (decodeUIntLE 1) (symbolStatusPresenceBits_ &&& 1 != 0) bytes
  let (symbolStatusRegulatoryHaltReason, bytes) ← decodeOptional (decodeUIntLE 1) (symbolStatusPresenceBits_ &&& 2 != 0) bytes
  if fits_symbolStatusPresenceBits : (symbolStatusPresenceBits_ &&& 252) &&& 3 = 0 then
    pure ({ symbolStatusPresenceBits := ⟨symbolStatusPresenceBits_ &&& 252, fits_symbolStatusPresenceBits⟩, transactTime, symbolId, symbolTradingState, shortSaleRestrictionState, symbolStatusOperationalHaltReason, symbolStatusRegulatoryHaltReason }, bytes)
  else none

theorem encode_length_pos (message : SymbolStatusMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

@[simp] theorem decode_encode (message : SymbolStatusMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  have selected_symbolStatusOperationalHaltReason : ((message.symbolStatusPresenceBits.val ||| presence (n := 8) 1 message.symbolStatusOperationalHaltReason.isSome ||| presence (n := 8) 2 message.symbolStatusRegulatoryHaltReason.isSome) &&& 1 != 0) = message.symbolStatusOperationalHaltReason.isSome := by
    have clear := message.symbolStatusPresenceBits.property
    simp only [presence]
    bv_decide
  have selected_symbolStatusRegulatoryHaltReason : ((message.symbolStatusPresenceBits.val ||| presence (n := 8) 1 message.symbolStatusOperationalHaltReason.isSome ||| presence (n := 8) 2 message.symbolStatusRegulatoryHaltReason.isSome) &&& 2 != 0) = message.symbolStatusRegulatoryHaltReason.isSome := by
    have clear := message.symbolStatusPresenceBits.property
    simp only [presence]
    bv_decide
  have carried_symbolStatusPresenceBits : (message.symbolStatusPresenceBits.val ||| presence (n := 8) 1 message.symbolStatusOperationalHaltReason.isSome ||| presence (n := 8) 2 message.symbolStatusRegulatoryHaltReason.isSome) &&& 252 = message.symbolStatusPresenceBits.val := by
    have clear := message.symbolStatusPresenceBits.property
    simp only [presence]
    bv_decide
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
  rw [selected_symbolStatusOperationalHaltReason]
  rw [List.append_assoc, decodeOptional_encodeOptional (encodeUIntLE 1) (decodeUIntLE 1) (decodeUIntLE_encodeUIntLE 1), some_bind]
  dsimp only
  rw [selected_symbolStatusRegulatoryHaltReason]
  rw [decodeOptional_encodeOptional (encodeUIntLE 1) (decodeUIntLE 1) (decodeUIntLE_encodeUIntLE 1), some_bind]
  dsimp only
  rw [dite_eq_left (by rw [carried_symbolStatusPresenceBits]; exact message.symbolStatusPresenceBits.property)]
  simp only [carried_symbolStatusPresenceBits]
  rfl

end SymbolStatusMessage

/-- Add Order Message: 31 bytes -/
structure AddOrderMessage where
  transactTime : BitVec 64
  symbolId : BitVec 16
  orderId : BitVec 64
  orderBitFields : BitVec 8
  price : BitVec 64
  qty : BitVec 32
  deriving DecidableEq, Repr

namespace AddOrderMessage

def encode (message : AddOrderMessage) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 2 message.symbolId
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 1 message.orderBitFields
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.qty)))))

def decode (bytes : List UInt8) : Option (AddOrderMessage × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (symbolId, bytes) ← decodeUIntLE 2 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (orderBitFields, bytes) ← decodeUIntLE 1 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (qty, bytes) ← decodeUIntLE 4 bytes
  pure ({ transactTime, symbolId, orderId, orderBitFields, price, qty }, bytes)

@[simp] theorem encode_length (message : AddOrderMessage) : (encode message).length = 31 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : AddOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AddOrderMessage) (rest : List UInt8) :
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

end AddOrderMessage

/-- Delete Order Message: 18 bytes -/
structure DeleteOrderMessage where
  transactTime : BitVec 64
  symbolId : BitVec 16
  orderId : BitVec 64
  deriving DecidableEq, Repr

namespace DeleteOrderMessage

def encode (message : DeleteOrderMessage) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 2 message.symbolId
    ++ (encodeUIntLE 8 message.orderId))

def decode (bytes : List UInt8) : Option (DeleteOrderMessage × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (symbolId, bytes) ← decodeUIntLE 2 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  pure ({ transactTime, symbolId, orderId }, bytes)

@[simp] theorem encode_length (message : DeleteOrderMessage) : (encode message).length = 18 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : DeleteOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DeleteOrderMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end DeleteOrderMessage

/-- Execute Order Message: 30 bytes -/
structure ExecuteOrderMessage where
  transactTime : BitVec 64
  symbolId : BitVec 16
  orderId : BitVec 64
  qty : BitVec 32
  execId : BitVec 64
  deriving DecidableEq, Repr

namespace ExecuteOrderMessage

def encode (message : ExecuteOrderMessage) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 2 message.symbolId
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 4 message.qty
    ++ (encodeUIntLE 8 message.execId))))

def decode (bytes : List UInt8) : Option (ExecuteOrderMessage × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (symbolId, bytes) ← decodeUIntLE 2 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (qty, bytes) ← decodeUIntLE 4 bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  pure ({ transactTime, symbolId, orderId, qty, execId }, bytes)

@[simp] theorem encode_length (message : ExecuteOrderMessage) : (encode message).length = 30 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : ExecuteOrderMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ExecuteOrderMessage) (rest : List UInt8) :
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

end ExecuteOrderMessage

/-- Execute Order With Price Message: 39 bytes -/
structure ExecuteOrderWithPriceMessage where
  transactTime : BitVec 64
  symbolId : BitVec 16
  orderId : BitVec 64
  qty : BitVec 32
  execId : BitVec 64
  execPrice : BitVec 64
  executionBitFields : BitVec 8
  deriving DecidableEq, Repr

namespace ExecuteOrderWithPriceMessage

def encode (message : ExecuteOrderWithPriceMessage) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 2 message.symbolId
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 4 message.qty
    ++ (encodeUIntLE 8 message.execId
    ++ (encodeUIntLE 8 message.execPrice
    ++ (encodeUIntLE 1 message.executionBitFields))))))

def decode (bytes : List UInt8) : Option (ExecuteOrderWithPriceMessage × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (symbolId, bytes) ← decodeUIntLE 2 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (qty, bytes) ← decodeUIntLE 4 bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  let (execPrice, bytes) ← decodeUIntLE 8 bytes
  let (executionBitFields, bytes) ← decodeUIntLE 1 bytes
  pure ({ transactTime, symbolId, orderId, qty, execId, execPrice, executionBitFields }, bytes)

@[simp] theorem encode_length (message : ExecuteOrderWithPriceMessage) : (encode message).length = 39 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : ExecuteOrderWithPriceMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ExecuteOrderWithPriceMessage) (rest : List UInt8) :
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

end ExecuteOrderWithPriceMessage

/-- Modify Size Down Message: 22 bytes -/
structure ModifySizeDownMessage where
  transactTime : BitVec 64
  symbolId : BitVec 16
  orderId : BitVec 64
  qty : BitVec 32
  deriving DecidableEq, Repr

namespace ModifySizeDownMessage

def encode (message : ModifySizeDownMessage) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 2 message.symbolId
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 4 message.qty)))

def decode (bytes : List UInt8) : Option (ModifySizeDownMessage × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (symbolId, bytes) ← decodeUIntLE 2 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (qty, bytes) ← decodeUIntLE 4 bytes
  pure ({ transactTime, symbolId, orderId, qty }, bytes)

@[simp] theorem encode_length (message : ModifySizeDownMessage) : (encode message).length = 22 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : ModifySizeDownMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ModifySizeDownMessage) (rest : List UInt8) :
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

end ModifySizeDownMessage

/-- Replace Order Message: 38 bytes -/
structure ReplaceOrderMessage where
  transactTime : BitVec 64
  symbolId : BitVec 16
  oldOrderId : BitVec 64
  newOrderId : BitVec 64
  price : BitVec 64
  qty : BitVec 32
  deriving DecidableEq, Repr

namespace ReplaceOrderMessage

def encode (message : ReplaceOrderMessage) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 2 message.symbolId
    ++ (encodeUIntLE 8 message.oldOrderId
    ++ (encodeUIntLE 8 message.newOrderId
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.qty)))))

def decode (bytes : List UInt8) : Option (ReplaceOrderMessage × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (symbolId, bytes) ← decodeUIntLE 2 bytes
  let (oldOrderId, bytes) ← decodeUIntLE 8 bytes
  let (newOrderId, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (qty, bytes) ← decodeUIntLE 4 bytes
  pure ({ transactTime, symbolId, oldOrderId, newOrderId, price, qty }, bytes)

@[simp] theorem encode_length (message : ReplaceOrderMessage) : (encode message).length = 38 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end ReplaceOrderMessage

/-- Trade Message: 30 bytes -/
structure TradeMessage where
  transactTime : BitVec 64
  symbolId : BitVec 16
  price : BitVec 64
  qty : BitVec 32
  execId : BitVec 64
  deriving DecidableEq, Repr

namespace TradeMessage

def encode (message : TradeMessage) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 2 message.symbolId
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.qty
    ++ (encodeUIntLE 8 message.execId))))

def decode (bytes : List UInt8) : Option (TradeMessage × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (symbolId, bytes) ← decodeUIntLE 2 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (qty, bytes) ← decodeUIntLE 4 bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  pure ({ transactTime, symbolId, price, qty, execId }, bytes)

@[simp] theorem encode_length (message : TradeMessage) : (encode message).length = 30 := by
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TradeMessage

/-- Break Trade Message: 18 bytes -/
structure BreakTradeMessage where
  transactTime : BitVec 64
  symbolId : BitVec 16
  execId : BitVec 64
  deriving DecidableEq, Repr

namespace BreakTradeMessage

def encode (message : BreakTradeMessage) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 2 message.symbolId
    ++ (encodeUIntLE 8 message.execId))

def decode (bytes : List UInt8) : Option (BreakTradeMessage × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (symbolId, bytes) ← decodeUIntLE 2 bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  pure ({ transactTime, symbolId, execId }, bytes)

@[simp] theorem encode_length (message : BreakTradeMessage) : (encode message).length = 18 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : BreakTradeMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BreakTradeMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end BreakTradeMessage

/-- Auction Preamble Message: 32 bytes -/
structure AuctionPreambleMessage where
  transactTime : BitVec 64
  symbolId : BitVec 16
  auctionType : BitVec 8
  auctionStart : BitVec 64
  matchedShares : BitVec 32
  excessAuctionSide : BitVec 8
  reserved8 : BitVec 64
  deriving DecidableEq, Repr

namespace AuctionPreambleMessage

def encode (message : AuctionPreambleMessage) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 2 message.symbolId
    ++ (encodeUIntLE 1 message.auctionType
    ++ (encodeUIntLE 8 message.auctionStart
    ++ (encodeUIntLE 4 message.matchedShares
    ++ (encodeUIntLE 1 message.excessAuctionSide
    ++ (encodeUIntLE 8 message.reserved8))))))

def decode (bytes : List UInt8) : Option (AuctionPreambleMessage × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (symbolId, bytes) ← decodeUIntLE 2 bytes
  let (auctionType, bytes) ← decodeUIntLE 1 bytes
  let (auctionStart, bytes) ← decodeUIntLE 8 bytes
  let (matchedShares, bytes) ← decodeUIntLE 4 bytes
  let (excessAuctionSide, bytes) ← decodeUIntLE 1 bytes
  let (reserved8, bytes) ← decodeUIntLE 8 bytes
  pure ({ transactTime, symbolId, auctionType, auctionStart, matchedShares, excessAuctionSide, reserved8 }, bytes)

@[simp] theorem encode_length (message : AuctionPreambleMessage) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : AuctionPreambleMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AuctionPreambleMessage) (rest : List UInt8) :
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

end AuctionPreambleMessage

/-- Auction Band Window Message: 60 bytes -/
structure AuctionBandWindowMessage where
  transactTime : BitVec 64
  symbolId : BitVec 16
  auctionType : BitVec 8
  auctionStart : BitVec 64
  extensionCycleCount : BitVec 8
  lowerParticipationBand : BitVec 64
  buySharesAtLower : BitVec 32
  sellSharesAtLower : BitVec 32
  upperParticipationBand : BitVec 64
  buySharesAtUpper : BitVec 32
  sellSharesAtUpper : BitVec 32
  reserved8 : BitVec 64
  deriving DecidableEq, Repr

namespace AuctionBandWindowMessage

def encode (message : AuctionBandWindowMessage) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 2 message.symbolId
    ++ (encodeUIntLE 1 message.auctionType
    ++ (encodeUIntLE 8 message.auctionStart
    ++ (encodeUIntLE 1 message.extensionCycleCount
    ++ (encodeUIntLE 8 message.lowerParticipationBand
    ++ (encodeUIntLE 4 message.buySharesAtLower
    ++ (encodeUIntLE 4 message.sellSharesAtLower
    ++ (encodeUIntLE 8 message.upperParticipationBand
    ++ (encodeUIntLE 4 message.buySharesAtUpper
    ++ (encodeUIntLE 4 message.sellSharesAtUpper
    ++ (encodeUIntLE 8 message.reserved8)))))))))))

def decode (bytes : List UInt8) : Option (AuctionBandWindowMessage × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (symbolId, bytes) ← decodeUIntLE 2 bytes
  let (auctionType, bytes) ← decodeUIntLE 1 bytes
  let (auctionStart, bytes) ← decodeUIntLE 8 bytes
  let (extensionCycleCount, bytes) ← decodeUIntLE 1 bytes
  let (lowerParticipationBand, bytes) ← decodeUIntLE 8 bytes
  let (buySharesAtLower, bytes) ← decodeUIntLE 4 bytes
  let (sellSharesAtLower, bytes) ← decodeUIntLE 4 bytes
  let (upperParticipationBand, bytes) ← decodeUIntLE 8 bytes
  let (buySharesAtUpper, bytes) ← decodeUIntLE 4 bytes
  let (sellSharesAtUpper, bytes) ← decodeUIntLE 4 bytes
  let (reserved8, bytes) ← decodeUIntLE 8 bytes
  pure ({ transactTime, symbolId, auctionType, auctionStart, extensionCycleCount, lowerParticipationBand, buySharesAtLower, sellSharesAtLower, upperParticipationBand, buySharesAtUpper, sellSharesAtUpper, reserved8 }, bytes)

@[simp] theorem encode_length (message : AuctionBandWindowMessage) : (encode message).length = 60 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : AuctionBandWindowMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AuctionBandWindowMessage) (rest : List UInt8) :
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end AuctionBandWindowMessage

/-- Auction Print Message: 31 bytes -/
structure AuctionPrintMessage where
  transactTime : BitVec 64
  symbolId : BitVec 16
  auctionType : BitVec 8
  auctionPrice : BitVec 64
  matchedShares : BitVec 32
  execId : BitVec 64
  deriving DecidableEq, Repr

namespace AuctionPrintMessage

def encode (message : AuctionPrintMessage) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 2 message.symbolId
    ++ (encodeUIntLE 1 message.auctionType
    ++ (encodeUIntLE 8 message.auctionPrice
    ++ (encodeUIntLE 4 message.matchedShares
    ++ (encodeUIntLE 8 message.execId)))))

def decode (bytes : List UInt8) : Option (AuctionPrintMessage × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (symbolId, bytes) ← decodeUIntLE 2 bytes
  let (auctionType, bytes) ← decodeUIntLE 1 bytes
  let (auctionPrice, bytes) ← decodeUIntLE 8 bytes
  let (matchedShares, bytes) ← decodeUIntLE 4 bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  pure ({ transactTime, symbolId, auctionType, auctionPrice, matchedShares, execId }, bytes)

@[simp] theorem encode_length (message : AuctionPrintMessage) : (encode message).length = 31 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : AuctionPrintMessage) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AuctionPrintMessage) (rest : List UInt8) :
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

end AuctionPrintMessage

/-- Any Payload, selected by Message Type -/
inductive Payload where
  | tradingSessionStatusMessage (message : TradingSessionStatusMessage) -- 105
  | defineSymbolMessage (message : DefineSymbolMessage) -- 115
  | symbolStatusMessage (message : SymbolStatusMessage) -- 121
  | addOrderMessage (message : AddOrderMessage) -- 97
  | deleteOrderMessage (message : DeleteOrderMessage) -- 100
  | executeOrderMessage (message : ExecuteOrderMessage) -- 101
  | executeOrderWithPriceMessage (message : ExecuteOrderWithPriceMessage) -- 112
  | modifySizeDownMessage (message : ModifySizeDownMessage) -- 109
  | replaceOrderMessage (message : ReplaceOrderMessage) -- 114
  | tradeMessage (message : TradeMessage) -- 116
  | breakTradeMessage (message : BreakTradeMessage) -- 98
  | auctionPreambleMessage (message : AuctionPreambleMessage) -- 117
  | auctionBandWindowMessage (message : AuctionBandWindowMessage) -- 118
  | auctionPrintMessage (message : AuctionPrintMessage) -- 110
  deriving DecidableEq, Repr

namespace Payload

/-- The Message Type each message is sent under -/
def tag : Payload → BitVec 8
  | .tradingSessionStatusMessage _ => 105
  | .defineSymbolMessage _ => 115
  | .symbolStatusMessage _ => 121
  | .addOrderMessage _ => 97
  | .deleteOrderMessage _ => 100
  | .executeOrderMessage _ => 101
  | .executeOrderWithPriceMessage _ => 112
  | .modifySizeDownMessage _ => 109
  | .replaceOrderMessage _ => 114
  | .tradeMessage _ => 116
  | .breakTradeMessage _ => 98
  | .auctionPreambleMessage _ => 117
  | .auctionBandWindowMessage _ => 118
  | .auctionPrintMessage _ => 110

def encode : Payload → List UInt8
  | .tradingSessionStatusMessage message => TradingSessionStatusMessage.encode message
  | .defineSymbolMessage message => DefineSymbolMessage.encode message
  | .symbolStatusMessage message => SymbolStatusMessage.encode message
  | .addOrderMessage message => AddOrderMessage.encode message
  | .deleteOrderMessage message => DeleteOrderMessage.encode message
  | .executeOrderMessage message => ExecuteOrderMessage.encode message
  | .executeOrderWithPriceMessage message => ExecuteOrderWithPriceMessage.encode message
  | .modifySizeDownMessage message => ModifySizeDownMessage.encode message
  | .replaceOrderMessage message => ReplaceOrderMessage.encode message
  | .tradeMessage message => TradeMessage.encode message
  | .breakTradeMessage message => BreakTradeMessage.encode message
  | .auctionPreambleMessage message => AuctionPreambleMessage.encode message
  | .auctionBandWindowMessage message => AuctionBandWindowMessage.encode message
  | .auctionPrintMessage message => AuctionPrintMessage.encode message

def decode (tag : BitVec 8) (bytes : List UInt8) : Option (Payload × List UInt8) :=
  if tag = 105 then (TradingSessionStatusMessage.decode bytes).map fun (message, rest) => (.tradingSessionStatusMessage message, rest)
  else if tag = 115 then (DefineSymbolMessage.decode bytes).map fun (message, rest) => (.defineSymbolMessage message, rest)
  else if tag = 121 then (SymbolStatusMessage.decode bytes).map fun (message, rest) => (.symbolStatusMessage message, rest)
  else if tag = 97 then (AddOrderMessage.decode bytes).map fun (message, rest) => (.addOrderMessage message, rest)
  else if tag = 100 then (DeleteOrderMessage.decode bytes).map fun (message, rest) => (.deleteOrderMessage message, rest)
  else if tag = 101 then (ExecuteOrderMessage.decode bytes).map fun (message, rest) => (.executeOrderMessage message, rest)
  else if tag = 112 then (ExecuteOrderWithPriceMessage.decode bytes).map fun (message, rest) => (.executeOrderWithPriceMessage message, rest)
  else if tag = 109 then (ModifySizeDownMessage.decode bytes).map fun (message, rest) => (.modifySizeDownMessage message, rest)
  else if tag = 114 then (ReplaceOrderMessage.decode bytes).map fun (message, rest) => (.replaceOrderMessage message, rest)
  else if tag = 116 then (TradeMessage.decode bytes).map fun (message, rest) => (.tradeMessage message, rest)
  else if tag = 98 then (BreakTradeMessage.decode bytes).map fun (message, rest) => (.breakTradeMessage message, rest)
  else if tag = 117 then (AuctionPreambleMessage.decode bytes).map fun (message, rest) => (.auctionPreambleMessage message, rest)
  else if tag = 118 then (AuctionBandWindowMessage.decode bytes).map fun (message, rest) => (.auctionBandWindowMessage message, rest)
  else if tag = 110 then (AuctionPrintMessage.decode bytes).map fun (message, rest) => (.auctionPrintMessage message, rest)
  else none

@[simp] theorem decode_encode (message : Payload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end Payload

/-- Udp Sequenced Message -/
structure UdpSequencedMessage where
  streamId : BitVec 8
  payload : Payload
  deriving DecidableEq, Repr

namespace UdpSequencedMessage

def encodeBody (message : UdpSequencedMessage) : List UInt8 :=
  encodeUInt 1 message.streamId
    ++ (encodeUInt 1 (Payload.tag message.payload)
    ++ (Payload.encode message.payload))

def decodeBody (bytes : List UInt8) : Option (UdpSequencedMessage × List UInt8) := do
  let (streamId, bytes) ← decodeUInt 1 bytes
  let (messageType, bytes) ← decodeUInt 1 bytes
  let (payload, bytes) ← Payload.decode messageType bytes
  pure ({ streamId, payload }, bytes)

theorem decodeBody_encodeBody (message : UdpSequencedMessage) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Payload.decode_encode, some_bind]
  rfl

/-- Size rule: Message Length counts the bytes after it, so it is written from the body; the body has no bound the prefix must fit, so it is read by its content and the prefix is not checked -/
def encode (message : UdpSequencedMessage) : List UInt8 :=
  encodeUIntLE 2 (BitVec.ofNat (8 * 2) ((encodeBody message).length + 0)) ++ encodeBody message

def decode (bytes : List UInt8) : Option (UdpSequencedMessage × List UInt8) := do
  let (_, bytes) ← decodeUIntLE 2 bytes
  decodeBody bytes

@[simp] theorem decode_encode (message : UdpSequencedMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  exact decodeBody_encodeBody message rest

theorem encode_length_pos (message : UdpSequencedMessage) : (encode message).length > 0 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]
  omega

end UdpSequencedMessage

/-- Packet -/
structure Packet where
  session : BitVec 64
  sequence : BitVec 64
  packetType : BitVec 8
  udpSequencedMessage : Bounded 2 UdpSequencedMessage
  deriving DecidableEq, Repr

namespace Packet

def encode (message : Packet) : List UInt8 :=
  encodeUIntLE 8 message.session
    ++ (encodeUIntLE 8 message.sequence
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.udpSequencedMessage.val.length)
    ++ (encodeUInt 1 message.packetType
    ++ (encodeMany UdpSequencedMessage.encode message.udpSequencedMessage.val))))

def decode (bytes : List UInt8) : Option (Packet × List UInt8) := do
  let (session, bytes) ← decodeUIntLE 8 bytes
  let (sequence, bytes) ← decodeUIntLE 8 bytes
  let (messageCount, bytes) ← decodeUIntLE 2 bytes
  let (packetType, bytes) ← decodeUInt 1 bytes
  let (udpSequencedMessage_, bytes) ← decodeMany UdpSequencedMessage.decode messageCount.toNat bytes
  if fits_udpSequencedMessage : udpSequencedMessage_.length < 256 ^ 2 then
    pure ({ session, sequence, packetType, udpSequencedMessage := ⟨udpSequencedMessage_, fits_udpSequencedMessage⟩ }, bytes)
  else none

theorem encode_length_pos (message : Packet) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

@[simp] theorem decode_encode (message : Packet) (rest : List UInt8) :
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
  rw [decodeMany_bounded 2 UdpSequencedMessage.encode UdpSequencedMessage.decode UdpSequencedMessage.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.udpSequencedMessage.length_lt]
  rfl

end Packet

end Omi.TxseTxseequitiesFeedRakeV10
