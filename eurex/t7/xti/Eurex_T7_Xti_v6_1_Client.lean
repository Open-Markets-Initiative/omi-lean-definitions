import Omi.Wire

/-!
# Eurex Exchange Cash Enhanced Trading Interface v6.1

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Cross Request is not framed: its length Body Len is not the integer that leads it.

Note: Delete All Order Request is not framed: its length Body Len is not the integer that leads it.

Note: Delete All Quote Request is not framed: its length Body Len is not the integer that leads it.

Note: Delete Order Single Request is not framed: its length Body Len is not the integer that leads it.

Note: Enter Best Quote Request is not framed: its length Body Len is not the integer that leads it.

Note: Gateway Request is not framed: its length Body Len is not the integer that leads it.

Note: Heartbeat is not framed: its length Body Len is not the integer that leads it.

Note: Inquire Enrichment Rule Id List Request is not framed: its length Body Len is not the integer that leads it.

Note: Inquire Session List Request is not framed: its length Body Len is not the integer that leads it.

Note: Inquire User Request is not framed: its length Body Len is not the integer that leads it.

Note: Logon Request is not framed: its length Body Len is not the integer that leads it.

Note: Logout Request is not framed: its length Body Len is not the integer that leads it.

Note: Mass Quote Request is not framed: its length Body Len is not the integer that leads it.

Note: Modify Order Single Request is not framed: its length Body Len is not the integer that leads it.

Note: Modify Order Single Short Request is not framed: its length Body Len is not the integer that leads it.

Note: New Order Single Request is not framed: its length Body Len is not the integer that leads it.

Note: New Order Single Short Request is not framed: its length Body Len is not the integer that leads it.

Note: Quote Activation Request is not framed: its length Body Len is not the integer that leads it.

Note: Rfq Request is not framed: its length Body Len is not the integer that leads it.

Note: Retransmit Me Message Request is not framed: its length Body Len is not the integer that leads it.

Note: Retransmit Request is not framed: its length Body Len is not the integer that leads it.

Note: Subscribe Request is not framed: its length Body Len is not the integer that leads it.

Note: Unsubscribe Request is not framed: its length Body Len is not the integer that leads it.

Note: User Login Request is not framed: its length Body Len is not the integer that leads it.

Note: User Logout Request is not framed: its length Body Len is not the integer that leads it.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.EurexT7XtiFbeV61Client

/-- Appl Usage Orders: one byte code -/
def ApplUsageOrders.codes : List UInt8 :=
  [0x41, 0x4D, 0x42, 0x4E]

inductive ApplUsageOrders where
  | automated -- Automated
  | manual -- Manual
  | autoSelect -- Auto Select
  | none_ -- None
  | unlisted (byte : { byte : UInt8 // byte ∉ ApplUsageOrders.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ApplUsageOrders

def toByte : ApplUsageOrders → UInt8
  | .automated => 0x41
  | .manual => 0x4D
  | .autoSelect => 0x42
  | .none_ => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ApplUsageOrders :=
  if byte = 0x41 then .automated
  else if byte = 0x4D then .manual
  else if byte = 0x42 then .autoSelect
  else .none_

def ofByte (byte : UInt8) : ApplUsageOrders :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ApplUsageOrders) : ofByte value.toByte = value := by
  cases value with
  | automated => decide
  | manual => decide
  | autoSelect => decide
  | none_ => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ApplUsageOrders) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ApplUsageOrders × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ApplUsageOrders) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ApplUsageOrders) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ApplUsageOrders

/-- Appl Usage Quotes: one byte code -/
def ApplUsageQuotes.codes : List UInt8 :=
  [0x41, 0x4D, 0x42, 0x4E]

inductive ApplUsageQuotes where
  | automated -- Automated
  | manual -- Manual
  | autoSelect -- Auto Select
  | none_ -- None
  | unlisted (byte : { byte : UInt8 // byte ∉ ApplUsageQuotes.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ApplUsageQuotes

def toByte : ApplUsageQuotes → UInt8
  | .automated => 0x41
  | .manual => 0x4D
  | .autoSelect => 0x42
  | .none_ => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ApplUsageQuotes :=
  if byte = 0x41 then .automated
  else if byte = 0x4D then .manual
  else if byte = 0x42 then .autoSelect
  else .none_

def ofByte (byte : UInt8) : ApplUsageQuotes :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ApplUsageQuotes) : ofByte value.toByte = value := by
  cases value with
  | automated => decide
  | manual => decide
  | autoSelect => decide
  | none_ => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ApplUsageQuotes) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ApplUsageQuotes × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ApplUsageQuotes) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ApplUsageQuotes) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ApplUsageQuotes

/-- Order Routing Indicator: one byte code -/
def OrderRoutingIndicator.codes : List UInt8 :=
  [0x59, 0x4E]

inductive OrderRoutingIndicator where
  | yes -- Yes
  | no -- No
  | unlisted (byte : { byte : UInt8 // byte ∉ OrderRoutingIndicator.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrderRoutingIndicator

def toByte : OrderRoutingIndicator → UInt8
  | .yes => 0x59
  | .no => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrderRoutingIndicator :=
  if byte = 0x59 then .yes
  else .no

def ofByte (byte : UInt8) : OrderRoutingIndicator :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrderRoutingIndicator) : ofByte value.toByte = value := by
  cases value with
  | yes => decide
  | no => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OrderRoutingIndicator) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OrderRoutingIndicator × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OrderRoutingIndicator) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OrderRoutingIndicator) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OrderRoutingIndicator

/-- Request Header Comp: 8 bytes -/
structure RequestHeaderComp where
  msgSeqNum : BitVec 32
  senderSubId : BitVec 32
  deriving DecidableEq, Repr

namespace RequestHeaderComp

def encode (message : RequestHeaderComp) : List UInt8 :=
  encodeUIntLE 4 message.msgSeqNum
    ++ encodeUIntLE 4 message.senderSubId

def decode (bytes : List UInt8) : Option (RequestHeaderComp × List UInt8) := do
  let (msgSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (senderSubId, bytes) ← decodeUIntLE 4 bytes
  pure ({ msgSeqNum, senderSubId }, bytes)

@[simp] theorem encode_length (message : RequestHeaderComp) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : RequestHeaderComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RequestHeaderComp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

end RequestHeaderComp

/-- Cross Request: 34 bytes -/
structure CrossRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  securityId : BitVec 64
  marketSegmentId : BitVec 32
  orderQty : BitVec 32
  deriving DecidableEq, Repr

namespace CrossRequest

def encode (message : CrossRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ Alpha.encode message.pad2
    ++ RequestHeaderComp.encode message.requestHeaderComp
    ++ encodeUIntLE 8 message.securityId
    ++ encodeUIntLE 4 message.marketSegmentId
    ++ encodeUIntLE 4 message.orderQty

def decode (bytes : List UInt8) : Option (CrossRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (orderQty, bytes) ← decodeUIntLE 4 bytes
  pure ({ networkMsgId, pad2, requestHeaderComp, securityId, marketSegmentId, orderQty }, bytes)

@[simp] theorem encode_length (message : CrossRequest) : (encode message).length = 34 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : CrossRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CrossRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [RequestHeaderComp.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

end CrossRequest

/-- Delete All Order Request: 66 bytes -/
structure DeleteAllOrderRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  securityId : BitVec 64
  price : BitVec 64
  partyIdInvestmentDecisionMaker : BitVec 64
  executingTrader : BitVec 64
  marketSegmentId : BitVec 32
  targetPartyIdSessionId : BitVec 32
  targetPartyIdExecutingTrader : BitVec 32
  side : BitVec 8
  partyIdInvestmentDecisionMakerQualifier : BitVec 8
  executingTraderQualifier : BitVec 8
  pad1 : Alpha 1
  deriving DecidableEq, Repr

namespace DeleteAllOrderRequest

def encode (message : DeleteAllOrderRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ Alpha.encode message.pad2
    ++ RequestHeaderComp.encode message.requestHeaderComp
    ++ encodeUIntLE 8 message.securityId
    ++ encodeUIntLE 8 message.price
    ++ encodeUIntLE 8 message.partyIdInvestmentDecisionMaker
    ++ encodeUIntLE 8 message.executingTrader
    ++ encodeUIntLE 4 message.marketSegmentId
    ++ encodeUIntLE 4 message.targetPartyIdSessionId
    ++ encodeUIntLE 4 message.targetPartyIdExecutingTrader
    ++ encodeUInt 1 message.side
    ++ encodeUInt 1 message.partyIdInvestmentDecisionMakerQualifier
    ++ encodeUInt 1 message.executingTraderQualifier
    ++ Alpha.encode message.pad1

def decode (bytes : List UInt8) : Option (DeleteAllOrderRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (partyIdInvestmentDecisionMaker, bytes) ← decodeUIntLE 8 bytes
  let (executingTrader, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (targetPartyIdSessionId, bytes) ← decodeUIntLE 4 bytes
  let (targetPartyIdExecutingTrader, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (partyIdInvestmentDecisionMakerQualifier, bytes) ← decodeUInt 1 bytes
  let (executingTraderQualifier, bytes) ← decodeUInt 1 bytes
  let (pad1, bytes) ← Alpha.decode 1 bytes
  pure ({ networkMsgId, pad2, requestHeaderComp, securityId, price, partyIdInvestmentDecisionMaker, executingTrader, marketSegmentId, targetPartyIdSessionId, targetPartyIdExecutingTrader, side, partyIdInvestmentDecisionMakerQualifier, executingTraderQualifier, pad1 }, bytes)

@[simp] theorem encode_length (message : DeleteAllOrderRequest) : (encode message).length = 66 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : DeleteAllOrderRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DeleteAllOrderRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [RequestHeaderComp.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end DeleteAllOrderRequest

/-- Delete All Quote Request: 50 bytes -/
structure DeleteAllQuoteRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  partyIdInvestmentDecisionMaker : BitVec 64
  executingTrader : BitVec 64
  marketSegmentId : BitVec 32
  targetPartyIdSessionId : BitVec 32
  partyIdInvestmentDecisionMakerQualifier : BitVec 8
  executingTraderQualifier : BitVec 8
  pad6 : Alpha 6
  deriving DecidableEq, Repr

namespace DeleteAllQuoteRequest

def encode (message : DeleteAllQuoteRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ Alpha.encode message.pad2
    ++ RequestHeaderComp.encode message.requestHeaderComp
    ++ encodeUIntLE 8 message.partyIdInvestmentDecisionMaker
    ++ encodeUIntLE 8 message.executingTrader
    ++ encodeUIntLE 4 message.marketSegmentId
    ++ encodeUIntLE 4 message.targetPartyIdSessionId
    ++ encodeUInt 1 message.partyIdInvestmentDecisionMakerQualifier
    ++ encodeUInt 1 message.executingTraderQualifier
    ++ Alpha.encode message.pad6

def decode (bytes : List UInt8) : Option (DeleteAllQuoteRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (partyIdInvestmentDecisionMaker, bytes) ← decodeUIntLE 8 bytes
  let (executingTrader, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (targetPartyIdSessionId, bytes) ← decodeUIntLE 4 bytes
  let (partyIdInvestmentDecisionMakerQualifier, bytes) ← decodeUInt 1 bytes
  let (executingTraderQualifier, bytes) ← decodeUInt 1 bytes
  let (pad6, bytes) ← Alpha.decode 6 bytes
  pure ({ networkMsgId, pad2, requestHeaderComp, partyIdInvestmentDecisionMaker, executingTrader, marketSegmentId, targetPartyIdSessionId, partyIdInvestmentDecisionMakerQualifier, executingTraderQualifier, pad6 }, bytes)

@[simp] theorem encode_length (message : DeleteAllQuoteRequest) : (encode message).length = 50 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : DeleteAllQuoteRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DeleteAllQuoteRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [RequestHeaderComp.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end DeleteAllQuoteRequest

/-- Delete Order Single Request: 98 bytes -/
structure DeleteOrderSingleRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  orderId : BitVec 64
  clOrdId : BitVec 64
  origClOrdId : BitVec 64
  securityId : BitVec 64
  partyIdInvestmentDecisionMaker : BitVec 64
  executingTrader : BitVec 64
  marketSegmentId : BitVec 32
  targetPartyIdSessionId : BitVec 32
  partyIdInvestmentDecisionMakerQualifier : BitVec 8
  executingTraderQualifier : BitVec 8
  fixClOrdId : Alpha 20
  pad2v2 : Alpha 2
  deriving DecidableEq, Repr

namespace DeleteOrderSingleRequest

def encode (message : DeleteOrderSingleRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ Alpha.encode message.pad2
    ++ RequestHeaderComp.encode message.requestHeaderComp
    ++ encodeUIntLE 8 message.orderId
    ++ encodeUIntLE 8 message.clOrdId
    ++ encodeUIntLE 8 message.origClOrdId
    ++ encodeUIntLE 8 message.securityId
    ++ encodeUIntLE 8 message.partyIdInvestmentDecisionMaker
    ++ encodeUIntLE 8 message.executingTrader
    ++ encodeUIntLE 4 message.marketSegmentId
    ++ encodeUIntLE 4 message.targetPartyIdSessionId
    ++ encodeUInt 1 message.partyIdInvestmentDecisionMakerQualifier
    ++ encodeUInt 1 message.executingTraderQualifier
    ++ Alpha.encode message.fixClOrdId
    ++ Alpha.encode message.pad2v2

def decode (bytes : List UInt8) : Option (DeleteOrderSingleRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (origClOrdId, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (partyIdInvestmentDecisionMaker, bytes) ← decodeUIntLE 8 bytes
  let (executingTrader, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (targetPartyIdSessionId, bytes) ← decodeUIntLE 4 bytes
  let (partyIdInvestmentDecisionMakerQualifier, bytes) ← decodeUInt 1 bytes
  let (executingTraderQualifier, bytes) ← decodeUInt 1 bytes
  let (fixClOrdId, bytes) ← Alpha.decode 20 bytes
  let (pad2v2, bytes) ← Alpha.decode 2 bytes
  pure ({ networkMsgId, pad2, requestHeaderComp, orderId, clOrdId, origClOrdId, securityId, partyIdInvestmentDecisionMaker, executingTrader, marketSegmentId, targetPartyIdSessionId, partyIdInvestmentDecisionMakerQualifier, executingTraderQualifier, fixClOrdId, pad2v2 }, bytes)

@[simp] theorem encode_length (message : DeleteOrderSingleRequest) : (encode message).length = 98 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : DeleteOrderSingleRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DeleteOrderSingleRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [RequestHeaderComp.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end DeleteOrderSingleRequest

/-- Enter Best Quote Request: 114 bytes -/
structure EnterBestQuoteRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  quoteId : BitVec 64
  securityId : BitVec 64
  bidPx : BitVec 64
  offerPx : BitVec 64
  pegOffsetValueBidPx : BitVec 64
  pegOffsetValueOfferPx : BitVec 64
  partyIdInvestmentDecisionMaker : BitVec 64
  executingTrader : BitVec 64
  bidSize : BitVec 32
  offerSize : BitVec 32
  reservedBidSize : BitVec 32
  reservedOfferSize : BitVec 32
  marketSegmentId : BitVec 32
  enrichmentRuleId : BitVec 16
  orderAttributeLiquidityProvision : BitVec 8
  valueCheckTypeQuantity : BitVec 8
  partyIdInvestmentDecisionMakerQualifier : BitVec 8
  executingTraderQualifier : BitVec 8
  pad6 : Alpha 6
  deriving DecidableEq, Repr

namespace EnterBestQuoteRequest

def encode (message : EnterBestQuoteRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ Alpha.encode message.pad2
    ++ RequestHeaderComp.encode message.requestHeaderComp
    ++ encodeUIntLE 8 message.quoteId
    ++ encodeUIntLE 8 message.securityId
    ++ encodeUIntLE 8 message.bidPx
    ++ encodeUIntLE 8 message.offerPx
    ++ encodeUIntLE 8 message.pegOffsetValueBidPx
    ++ encodeUIntLE 8 message.pegOffsetValueOfferPx
    ++ encodeUIntLE 8 message.partyIdInvestmentDecisionMaker
    ++ encodeUIntLE 8 message.executingTrader
    ++ encodeUIntLE 4 message.bidSize
    ++ encodeUIntLE 4 message.offerSize
    ++ encodeUIntLE 4 message.reservedBidSize
    ++ encodeUIntLE 4 message.reservedOfferSize
    ++ encodeUIntLE 4 message.marketSegmentId
    ++ encodeUIntLE 2 message.enrichmentRuleId
    ++ encodeUInt 1 message.orderAttributeLiquidityProvision
    ++ encodeUInt 1 message.valueCheckTypeQuantity
    ++ encodeUInt 1 message.partyIdInvestmentDecisionMakerQualifier
    ++ encodeUInt 1 message.executingTraderQualifier
    ++ Alpha.encode message.pad6

def decode (bytes : List UInt8) : Option (EnterBestQuoteRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (quoteId, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (bidPx, bytes) ← decodeUIntLE 8 bytes
  let (offerPx, bytes) ← decodeUIntLE 8 bytes
  let (pegOffsetValueBidPx, bytes) ← decodeUIntLE 8 bytes
  let (pegOffsetValueOfferPx, bytes) ← decodeUIntLE 8 bytes
  let (partyIdInvestmentDecisionMaker, bytes) ← decodeUIntLE 8 bytes
  let (executingTrader, bytes) ← decodeUIntLE 8 bytes
  let (bidSize, bytes) ← decodeUIntLE 4 bytes
  let (offerSize, bytes) ← decodeUIntLE 4 bytes
  let (reservedBidSize, bytes) ← decodeUIntLE 4 bytes
  let (reservedOfferSize, bytes) ← decodeUIntLE 4 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (enrichmentRuleId, bytes) ← decodeUIntLE 2 bytes
  let (orderAttributeLiquidityProvision, bytes) ← decodeUInt 1 bytes
  let (valueCheckTypeQuantity, bytes) ← decodeUInt 1 bytes
  let (partyIdInvestmentDecisionMakerQualifier, bytes) ← decodeUInt 1 bytes
  let (executingTraderQualifier, bytes) ← decodeUInt 1 bytes
  let (pad6, bytes) ← Alpha.decode 6 bytes
  pure ({ networkMsgId, pad2, requestHeaderComp, quoteId, securityId, bidPx, offerPx, pegOffsetValueBidPx, pegOffsetValueOfferPx, partyIdInvestmentDecisionMaker, executingTrader, bidSize, offerSize, reservedBidSize, reservedOfferSize, marketSegmentId, enrichmentRuleId, orderAttributeLiquidityProvision, valueCheckTypeQuantity, partyIdInvestmentDecisionMakerQualifier, executingTraderQualifier, pad6 }, bytes)

@[simp] theorem encode_length (message : EnterBestQuoteRequest) : (encode message).length = 114 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : EnterBestQuoteRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EnterBestQuoteRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [RequestHeaderComp.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end EnterBestQuoteRequest

/-- Gateway Request: 90 bytes -/
structure GatewayRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  partyIdSessionId : BitVec 32
  partitionId : BitVec 16
  defaultCstmApplVerId : Alpha 30
  password : Alpha 32
  pad4 : Alpha 4
  deriving DecidableEq, Repr

namespace GatewayRequest

def encode (message : GatewayRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ Alpha.encode message.pad2
    ++ RequestHeaderComp.encode message.requestHeaderComp
    ++ encodeUIntLE 4 message.partyIdSessionId
    ++ encodeUIntLE 2 message.partitionId
    ++ Alpha.encode message.defaultCstmApplVerId
    ++ Alpha.encode message.password
    ++ Alpha.encode message.pad4

def decode (bytes : List UInt8) : Option (GatewayRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (partyIdSessionId, bytes) ← decodeUIntLE 4 bytes
  let (partitionId, bytes) ← decodeUIntLE 2 bytes
  let (defaultCstmApplVerId, bytes) ← Alpha.decode 30 bytes
  let (password, bytes) ← Alpha.decode 32 bytes
  let (pad4, bytes) ← Alpha.decode 4 bytes
  pure ({ networkMsgId, pad2, requestHeaderComp, partyIdSessionId, partitionId, defaultCstmApplVerId, password, pad4 }, bytes)

@[simp] theorem encode_length (message : GatewayRequest) : (encode message).length = 90 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : GatewayRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : GatewayRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [RequestHeaderComp.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end GatewayRequest

/-- Heartbeat: 10 bytes -/
structure Heartbeat where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  deriving DecidableEq, Repr

namespace Heartbeat

def encode (message : Heartbeat) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ Alpha.encode message.pad2

def decode (bytes : List UInt8) : Option (Heartbeat × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  pure ({ networkMsgId, pad2 }, bytes)

@[simp] theorem encode_length (message : Heartbeat) : (encode message).length = 10 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : Heartbeat) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : Heartbeat) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end Heartbeat

/-- Inquire Enrichment Rule Id List Request: 34 bytes -/
structure InquireEnrichmentRuleIdListRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  lastEntityProcessed : Alpha 16
  deriving DecidableEq, Repr

namespace InquireEnrichmentRuleIdListRequest

def encode (message : InquireEnrichmentRuleIdListRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ Alpha.encode message.pad2
    ++ RequestHeaderComp.encode message.requestHeaderComp
    ++ Alpha.encode message.lastEntityProcessed

def decode (bytes : List UInt8) : Option (InquireEnrichmentRuleIdListRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (lastEntityProcessed, bytes) ← Alpha.decode 16 bytes
  pure ({ networkMsgId, pad2, requestHeaderComp, lastEntityProcessed }, bytes)

@[simp] theorem encode_length (message : InquireEnrichmentRuleIdListRequest) : (encode message).length = 34 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RequestHeaderComp.encode_length]

theorem encode_length_pos (message : InquireEnrichmentRuleIdListRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InquireEnrichmentRuleIdListRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [RequestHeaderComp.decode_encode, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end InquireEnrichmentRuleIdListRequest

/-- Inquire Session List Request: 18 bytes -/
structure InquireSessionListRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  deriving DecidableEq, Repr

namespace InquireSessionListRequest

def encode (message : InquireSessionListRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ Alpha.encode message.pad2
    ++ RequestHeaderComp.encode message.requestHeaderComp

def decode (bytes : List UInt8) : Option (InquireSessionListRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  pure ({ networkMsgId, pad2, requestHeaderComp }, bytes)

@[simp] theorem encode_length (message : InquireSessionListRequest) : (encode message).length = 18 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RequestHeaderComp.encode_length]

theorem encode_length_pos (message : InquireSessionListRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InquireSessionListRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [RequestHeaderComp.decode_encode, Option.bind_some]
  rfl

end InquireSessionListRequest

/-- Inquire User Request: 34 bytes -/
structure InquireUserRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  lastEntityProcessed : Alpha 16
  deriving DecidableEq, Repr

namespace InquireUserRequest

def encode (message : InquireUserRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ Alpha.encode message.pad2
    ++ RequestHeaderComp.encode message.requestHeaderComp
    ++ Alpha.encode message.lastEntityProcessed

def decode (bytes : List UInt8) : Option (InquireUserRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (lastEntityProcessed, bytes) ← Alpha.decode 16 bytes
  pure ({ networkMsgId, pad2, requestHeaderComp, lastEntityProcessed }, bytes)

@[simp] theorem encode_length (message : InquireUserRequest) : (encode message).length = 34 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RequestHeaderComp.encode_length]

theorem encode_length_pos (message : InquireUserRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InquireUserRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [RequestHeaderComp.decode_encode, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end InquireUserRequest

/-- Logon Request: 274 bytes -/
structure LogonRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  heartBtInt : BitVec 32
  partyIdSessionId : BitVec 32
  defaultCstmApplVerId : Alpha 30
  password : Alpha 32
  applUsageOrders : ApplUsageOrders
  applUsageQuotes : ApplUsageQuotes
  orderRoutingIndicator : OrderRoutingIndicator
  fixEngineName : Alpha 30
  fixEngineVersion : Alpha 30
  fixEngineVendor : Alpha 30
  applicationSystemName : Alpha 30
  applicationSystemVersion : Alpha 30
  applicationSystemVendor : Alpha 30
  pad3 : Alpha 3
  deriving DecidableEq, Repr

namespace LogonRequest

def encode (message : LogonRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ Alpha.encode message.pad2
    ++ RequestHeaderComp.encode message.requestHeaderComp
    ++ encodeUIntLE 4 message.heartBtInt
    ++ encodeUIntLE 4 message.partyIdSessionId
    ++ Alpha.encode message.defaultCstmApplVerId
    ++ Alpha.encode message.password
    ++ ApplUsageOrders.encode message.applUsageOrders
    ++ ApplUsageQuotes.encode message.applUsageQuotes
    ++ OrderRoutingIndicator.encode message.orderRoutingIndicator
    ++ Alpha.encode message.fixEngineName
    ++ Alpha.encode message.fixEngineVersion
    ++ Alpha.encode message.fixEngineVendor
    ++ Alpha.encode message.applicationSystemName
    ++ Alpha.encode message.applicationSystemVersion
    ++ Alpha.encode message.applicationSystemVendor
    ++ Alpha.encode message.pad3

def decode (bytes : List UInt8) : Option (LogonRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (heartBtInt, bytes) ← decodeUIntLE 4 bytes
  let (partyIdSessionId, bytes) ← decodeUIntLE 4 bytes
  let (defaultCstmApplVerId, bytes) ← Alpha.decode 30 bytes
  let (password, bytes) ← Alpha.decode 32 bytes
  let (applUsageOrders, bytes) ← ApplUsageOrders.decode bytes
  let (applUsageQuotes, bytes) ← ApplUsageQuotes.decode bytes
  let (orderRoutingIndicator, bytes) ← OrderRoutingIndicator.decode bytes
  let (fixEngineName, bytes) ← Alpha.decode 30 bytes
  let (fixEngineVersion, bytes) ← Alpha.decode 30 bytes
  let (fixEngineVendor, bytes) ← Alpha.decode 30 bytes
  let (applicationSystemName, bytes) ← Alpha.decode 30 bytes
  let (applicationSystemVersion, bytes) ← Alpha.decode 30 bytes
  let (applicationSystemVendor, bytes) ← Alpha.decode 30 bytes
  let (pad3, bytes) ← Alpha.decode 3 bytes
  pure ({ networkMsgId, pad2, requestHeaderComp, heartBtInt, partyIdSessionId, defaultCstmApplVerId, password, applUsageOrders, applUsageQuotes, orderRoutingIndicator, fixEngineName, fixEngineVersion, fixEngineVendor, applicationSystemName, applicationSystemVersion, applicationSystemVendor, pad3 }, bytes)

@[simp] theorem encode_length (message : LogonRequest) : (encode message).length = 274 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length, ApplUsageOrders.encode_length, ApplUsageQuotes.encode_length, OrderRoutingIndicator.encode_length]

theorem encode_length_pos (message : LogonRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LogonRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [RequestHeaderComp.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [ApplUsageOrders.decode_encode, Option.bind_some]
  dsimp only
  rw [ApplUsageQuotes.decode_encode, Option.bind_some]
  dsimp only
  rw [OrderRoutingIndicator.decode_encode, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end LogonRequest

/-- Logout Request: 18 bytes -/
structure LogoutRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  deriving DecidableEq, Repr

namespace LogoutRequest

def encode (message : LogoutRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ Alpha.encode message.pad2
    ++ RequestHeaderComp.encode message.requestHeaderComp

def decode (bytes : List UInt8) : Option (LogoutRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  pure ({ networkMsgId, pad2, requestHeaderComp }, bytes)

@[simp] theorem encode_length (message : LogoutRequest) : (encode message).length = 18 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RequestHeaderComp.encode_length]

theorem encode_length_pos (message : LogoutRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LogoutRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [RequestHeaderComp.decode_encode, Option.bind_some]
  rfl

end LogoutRequest

/-- Quote Entry Grp Comp: 32 bytes -/
structure QuoteEntryGrpComp where
  securityId : BitVec 64
  bidPx : BitVec 64
  offerPx : BitVec 64
  bidSize : BitVec 32
  offerSize : BitVec 32
  deriving DecidableEq, Repr

namespace QuoteEntryGrpComp

def encode (message : QuoteEntryGrpComp) : List UInt8 :=
  encodeUIntLE 8 message.securityId
    ++ encodeUIntLE 8 message.bidPx
    ++ encodeUIntLE 8 message.offerPx
    ++ encodeUIntLE 4 message.bidSize
    ++ encodeUIntLE 4 message.offerSize

def decode (bytes : List UInt8) : Option (QuoteEntryGrpComp × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (bidPx, bytes) ← decodeUIntLE 8 bytes
  let (offerPx, bytes) ← decodeUIntLE 8 bytes
  let (bidSize, bytes) ← decodeUIntLE 4 bytes
  let (offerSize, bytes) ← decodeUIntLE 4 bytes
  pure ({ securityId, bidPx, offerPx, bidSize, offerSize }, bytes)

@[simp] theorem encode_length (message : QuoteEntryGrpComp) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : QuoteEntryGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : QuoteEntryGrpComp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

end QuoteEntryGrpComp

/-- Mass Quote Request -/
structure MassQuoteRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  quoteId : BitVec 64
  partyIdInvestmentDecisionMaker : BitVec 64
  executingTrader : BitVec 64
  marketSegmentId : BitVec 32
  matchInstCrossId : BitVec 32
  enrichmentRuleId : BitVec 16
  priceValidityCheckType : BitVec 8
  valueCheckTypeValue : BitVec 8
  valueCheckTypeQuantity : BitVec 8
  quoteSizeType : BitVec 8
  orderAttributeLiquidityProvision : BitVec 8
  partyIdInvestmentDecisionMakerQualifier : BitVec 8
  executingTraderQualifier : BitVec 8
  pad6 : Alpha 6
  quoteEntryGrpComp : Bounded 1 QuoteEntryGrpComp
  deriving DecidableEq, Repr

namespace MassQuoteRequest

def encode (message : MassQuoteRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ Alpha.encode message.pad2
    ++ RequestHeaderComp.encode message.requestHeaderComp
    ++ encodeUIntLE 8 message.quoteId
    ++ encodeUIntLE 8 message.partyIdInvestmentDecisionMaker
    ++ encodeUIntLE 8 message.executingTrader
    ++ encodeUIntLE 4 message.marketSegmentId
    ++ encodeUIntLE 4 message.matchInstCrossId
    ++ encodeUIntLE 2 message.enrichmentRuleId
    ++ encodeUInt 1 message.priceValidityCheckType
    ++ encodeUInt 1 message.valueCheckTypeValue
    ++ encodeUInt 1 message.valueCheckTypeQuantity
    ++ encodeUInt 1 message.quoteSizeType
    ++ encodeUInt 1 message.orderAttributeLiquidityProvision
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.quoteEntryGrpComp.val.length)
    ++ encodeUInt 1 message.partyIdInvestmentDecisionMakerQualifier
    ++ encodeUInt 1 message.executingTraderQualifier
    ++ Alpha.encode message.pad6
    ++ encodeMany QuoteEntryGrpComp.encode message.quoteEntryGrpComp.val

def decode (bytes : List UInt8) : Option (MassQuoteRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (quoteId, bytes) ← decodeUIntLE 8 bytes
  let (partyIdInvestmentDecisionMaker, bytes) ← decodeUIntLE 8 bytes
  let (executingTrader, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (matchInstCrossId, bytes) ← decodeUIntLE 4 bytes
  let (enrichmentRuleId, bytes) ← decodeUIntLE 2 bytes
  let (priceValidityCheckType, bytes) ← decodeUInt 1 bytes
  let (valueCheckTypeValue, bytes) ← decodeUInt 1 bytes
  let (valueCheckTypeQuantity, bytes) ← decodeUInt 1 bytes
  let (quoteSizeType, bytes) ← decodeUInt 1 bytes
  let (orderAttributeLiquidityProvision, bytes) ← decodeUInt 1 bytes
  let (noQuoteEntries, bytes) ← decodeUInt 1 bytes
  let (partyIdInvestmentDecisionMakerQualifier, bytes) ← decodeUInt 1 bytes
  let (executingTraderQualifier, bytes) ← decodeUInt 1 bytes
  let (pad6, bytes) ← Alpha.decode 6 bytes
  let (quoteEntryGrpComp_, bytes) ← decodeMany QuoteEntryGrpComp.decode noQuoteEntries.toNat bytes
  if fits_quoteEntryGrpComp : quoteEntryGrpComp_.length < 256 ^ 1 then
    pure ({ networkMsgId, pad2, requestHeaderComp, quoteId, partyIdInvestmentDecisionMaker, executingTrader, marketSegmentId, matchInstCrossId, enrichmentRuleId, priceValidityCheckType, valueCheckTypeValue, valueCheckTypeQuantity, quoteSizeType, orderAttributeLiquidityProvision, partyIdInvestmentDecisionMakerQualifier, executingTraderQualifier, pad6, quoteEntryGrpComp := ⟨quoteEntryGrpComp_, fits_quoteEntryGrpComp⟩ }, bytes)
  else none

theorem encode_length_pos (message : MassQuoteRequest) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MassQuoteRequest) : (encode message).length ≤ 8226 := by
  have bound_quoteEntryGrpComp := message.quoteEntryGrpComp.length_lt
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const QuoteEntryGrpComp.encode 32 QuoteEntryGrpComp.encode_length]
  omega

@[simp] theorem decode_encode (message : MassQuoteRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [RequestHeaderComp.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeMany_bounded 1 QuoteEntryGrpComp.encode QuoteEntryGrpComp.decode QuoteEntryGrpComp.decode_encode, Option.bind_some]
  dsimp only
  simp only [message.quoteEntryGrpComp.length_lt, ↓reduceDIte]
  rfl

end MassQuoteRequest

/-- Modify Order Single Request: 226 bytes -/
structure ModifyOrderSingleRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  orderId : BitVec 64
  clOrdId : BitVec 64
  origClOrdId : BitVec 64
  securityId : BitVec 64
  price : BitVec 64
  stopPx : BitVec 64
  volumeDiscoveryPrice : BitVec 64
  pegOffsetValueAbs : BitVec 64
  pegOffsetValuePct : BitVec 64
  partyIdClientId : BitVec 64
  partyIdInvestmentDecisionMaker : BitVec 64
  executingTrader : BitVec 64
  orderQty : BitVec 32
  displayQty : BitVec 32
  displayLowQty : BitVec 32
  displayHighQty : BitVec 32
  expireDate : BitVec 32
  marketSegmentId : BitVec 32
  matchInstCrossId : BitVec 32
  targetPartyIdSessionId : BitVec 32
  applSeqIndicator : BitVec 8
  side : BitVec 8
  ordType : BitVec 8
  priceValidityCheckType : BitVec 8
  valueCheckTypeValue : BitVec 8
  valueCheckTypeQuantity : BitVec 8
  orderAttributeLiquidityProvision : BitVec 8
  timeInForce : BitVec 8
  execInst : BitVec 8
  tradingSessionSubId : BitVec 8
  stopPxIndicator : BitVec 8
  tradingCapacity : BitVec 8
  exDestinationType : BitVec 8
  partyIdInvestmentDecisionMakerQualifier : BitVec 8
  executingTraderQualifier : BitVec 8
  ownershipIndicator : BitVec 8
  freeText1 : Alpha 12
  freeText2 : Alpha 12
  freeText4 : Alpha 16
  fixClOrdId : Alpha 20
  pad4 : Alpha 4
  deriving DecidableEq, Repr

namespace ModifyOrderSingleRequest

def encode (message : ModifyOrderSingleRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ Alpha.encode message.pad2
    ++ RequestHeaderComp.encode message.requestHeaderComp
    ++ encodeUIntLE 8 message.orderId
    ++ encodeUIntLE 8 message.clOrdId
    ++ encodeUIntLE 8 message.origClOrdId
    ++ encodeUIntLE 8 message.securityId
    ++ encodeUIntLE 8 message.price
    ++ encodeUIntLE 8 message.stopPx
    ++ encodeUIntLE 8 message.volumeDiscoveryPrice
    ++ encodeUIntLE 8 message.pegOffsetValueAbs
    ++ encodeUIntLE 8 message.pegOffsetValuePct
    ++ encodeUIntLE 8 message.partyIdClientId
    ++ encodeUIntLE 8 message.partyIdInvestmentDecisionMaker
    ++ encodeUIntLE 8 message.executingTrader
    ++ encodeUIntLE 4 message.orderQty
    ++ encodeUIntLE 4 message.displayQty
    ++ encodeUIntLE 4 message.displayLowQty
    ++ encodeUIntLE 4 message.displayHighQty
    ++ encodeUIntLE 4 message.expireDate
    ++ encodeUIntLE 4 message.marketSegmentId
    ++ encodeUIntLE 4 message.matchInstCrossId
    ++ encodeUIntLE 4 message.targetPartyIdSessionId
    ++ encodeUInt 1 message.applSeqIndicator
    ++ encodeUInt 1 message.side
    ++ encodeUInt 1 message.ordType
    ++ encodeUInt 1 message.priceValidityCheckType
    ++ encodeUInt 1 message.valueCheckTypeValue
    ++ encodeUInt 1 message.valueCheckTypeQuantity
    ++ encodeUInt 1 message.orderAttributeLiquidityProvision
    ++ encodeUInt 1 message.timeInForce
    ++ encodeUInt 1 message.execInst
    ++ encodeUInt 1 message.tradingSessionSubId
    ++ encodeUInt 1 message.stopPxIndicator
    ++ encodeUInt 1 message.tradingCapacity
    ++ encodeUInt 1 message.exDestinationType
    ++ encodeUInt 1 message.partyIdInvestmentDecisionMakerQualifier
    ++ encodeUInt 1 message.executingTraderQualifier
    ++ encodeUInt 1 message.ownershipIndicator
    ++ Alpha.encode message.freeText1
    ++ Alpha.encode message.freeText2
    ++ Alpha.encode message.freeText4
    ++ Alpha.encode message.fixClOrdId
    ++ Alpha.encode message.pad4

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (ModifyOrderSingleRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (origClOrdId, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (stopPx, bytes) ← decodeUIntLE 8 bytes
  let (volumeDiscoveryPrice, bytes) ← decodeUIntLE 8 bytes
  let (pegOffsetValueAbs, bytes) ← decodeUIntLE 8 bytes
  let (pegOffsetValuePct, bytes) ← decodeUIntLE 8 bytes
  let (partyIdClientId, bytes) ← decodeUIntLE 8 bytes
  let (partyIdInvestmentDecisionMaker, bytes) ← decodeUIntLE 8 bytes
  let (executingTrader, bytes) ← decodeUIntLE 8 bytes
  let (orderQty, bytes) ← decodeUIntLE 4 bytes
  let (displayQty, bytes) ← decodeUIntLE 4 bytes
  let (displayLowQty, bytes) ← decodeUIntLE 4 bytes
  let (displayHighQty, bytes) ← decodeUIntLE 4 bytes
  let (expireDate, bytes) ← decodeUIntLE 4 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (matchInstCrossId, bytes) ← decodeUIntLE 4 bytes
  let (targetPartyIdSessionId, bytes) ← decodeUIntLE 4 bytes
  let (applSeqIndicator, bytes) ← decodeUInt 1 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (ordType, bytes) ← decodeUInt 1 bytes
  let (priceValidityCheckType, bytes) ← decodeUInt 1 bytes
  let (valueCheckTypeValue, bytes) ← decodeUInt 1 bytes
  let (valueCheckTypeQuantity, bytes) ← decodeUInt 1 bytes
  let (orderAttributeLiquidityProvision, bytes) ← decodeUInt 1 bytes
  let (timeInForce, bytes) ← decodeUInt 1 bytes
  let (execInst, bytes) ← decodeUInt 1 bytes
  let (tradingSessionSubId, bytes) ← decodeUInt 1 bytes
  let (stopPxIndicator, bytes) ← decodeUInt 1 bytes
  let (tradingCapacity, bytes) ← decodeUInt 1 bytes
  let (exDestinationType, bytes) ← decodeUInt 1 bytes
  let (partyIdInvestmentDecisionMakerQualifier, bytes) ← decodeUInt 1 bytes
  let (executingTraderQualifier, bytes) ← decodeUInt 1 bytes
  let (ownershipIndicator, bytes) ← decodeUInt 1 bytes
  let (freeText1, bytes) ← Alpha.decode 12 bytes
  let (freeText2, bytes) ← Alpha.decode 12 bytes
  let (freeText4, bytes) ← Alpha.decode 16 bytes
  let (fixClOrdId, bytes) ← Alpha.decode 20 bytes
  let (pad4, bytes) ← Alpha.decode 4 bytes
  pure ({ networkMsgId, pad2, requestHeaderComp, orderId, clOrdId, origClOrdId, securityId, price, stopPx, volumeDiscoveryPrice, pegOffsetValueAbs, pegOffsetValuePct, partyIdClientId, partyIdInvestmentDecisionMaker, executingTrader, orderQty, displayQty, displayLowQty, displayHighQty, expireDate, marketSegmentId, matchInstCrossId, targetPartyIdSessionId, applSeqIndicator, side, ordType, priceValidityCheckType, valueCheckTypeValue, valueCheckTypeQuantity, orderAttributeLiquidityProvision, timeInForce, execInst, tradingSessionSubId, stopPxIndicator, tradingCapacity, exDestinationType, partyIdInvestmentDecisionMakerQualifier, executingTraderQualifier, ownershipIndicator, freeText1, freeText2, freeText4, fixClOrdId, pad4 }, bytes)

@[simp] theorem encode_length (message : ModifyOrderSingleRequest) : (encode message).length = 226 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : ModifyOrderSingleRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : ModifyOrderSingleRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [RequestHeaderComp.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end ModifyOrderSingleRequest

/-- Modify Order Single Short Request: 98 bytes -/
structure ModifyOrderSingleShortRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  clOrdId : BitVec 64
  origClOrdId : BitVec 64
  securityId : BitVec 64
  price : BitVec 64
  partyIdClientId : BitVec 64
  partyIdInvestmentDecisionMaker : BitVec 64
  executingTrader : BitVec 64
  orderQty : BitVec 32
  matchInstCrossId : BitVec 32
  enrichmentRuleId : BitVec 16
  side : BitVec 8
  priceValidityCheckType : BitVec 8
  valueCheckTypeValue : BitVec 8
  valueCheckTypeQuantity : BitVec 8
  orderAttributeLiquidityProvision : BitVec 8
  timeInForce : BitVec 8
  applSeqIndicator : BitVec 8
  execInst : BitVec 8
  tradingCapacity : BitVec 8
  exDestinationType : BitVec 8
  partyIdInvestmentDecisionMakerQualifier : BitVec 8
  executingTraderQualifier : BitVec 8
  pad2v2 : Alpha 2
  deriving DecidableEq, Repr

namespace ModifyOrderSingleShortRequest

def encode (message : ModifyOrderSingleShortRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ Alpha.encode message.pad2
    ++ RequestHeaderComp.encode message.requestHeaderComp
    ++ encodeUIntLE 8 message.clOrdId
    ++ encodeUIntLE 8 message.origClOrdId
    ++ encodeUIntLE 8 message.securityId
    ++ encodeUIntLE 8 message.price
    ++ encodeUIntLE 8 message.partyIdClientId
    ++ encodeUIntLE 8 message.partyIdInvestmentDecisionMaker
    ++ encodeUIntLE 8 message.executingTrader
    ++ encodeUIntLE 4 message.orderQty
    ++ encodeUIntLE 4 message.matchInstCrossId
    ++ encodeUIntLE 2 message.enrichmentRuleId
    ++ encodeUInt 1 message.side
    ++ encodeUInt 1 message.priceValidityCheckType
    ++ encodeUInt 1 message.valueCheckTypeValue
    ++ encodeUInt 1 message.valueCheckTypeQuantity
    ++ encodeUInt 1 message.orderAttributeLiquidityProvision
    ++ encodeUInt 1 message.timeInForce
    ++ encodeUInt 1 message.applSeqIndicator
    ++ encodeUInt 1 message.execInst
    ++ encodeUInt 1 message.tradingCapacity
    ++ encodeUInt 1 message.exDestinationType
    ++ encodeUInt 1 message.partyIdInvestmentDecisionMakerQualifier
    ++ encodeUInt 1 message.executingTraderQualifier
    ++ Alpha.encode message.pad2v2

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (ModifyOrderSingleShortRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (origClOrdId, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (partyIdClientId, bytes) ← decodeUIntLE 8 bytes
  let (partyIdInvestmentDecisionMaker, bytes) ← decodeUIntLE 8 bytes
  let (executingTrader, bytes) ← decodeUIntLE 8 bytes
  let (orderQty, bytes) ← decodeUIntLE 4 bytes
  let (matchInstCrossId, bytes) ← decodeUIntLE 4 bytes
  let (enrichmentRuleId, bytes) ← decodeUIntLE 2 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (priceValidityCheckType, bytes) ← decodeUInt 1 bytes
  let (valueCheckTypeValue, bytes) ← decodeUInt 1 bytes
  let (valueCheckTypeQuantity, bytes) ← decodeUInt 1 bytes
  let (orderAttributeLiquidityProvision, bytes) ← decodeUInt 1 bytes
  let (timeInForce, bytes) ← decodeUInt 1 bytes
  let (applSeqIndicator, bytes) ← decodeUInt 1 bytes
  let (execInst, bytes) ← decodeUInt 1 bytes
  let (tradingCapacity, bytes) ← decodeUInt 1 bytes
  let (exDestinationType, bytes) ← decodeUInt 1 bytes
  let (partyIdInvestmentDecisionMakerQualifier, bytes) ← decodeUInt 1 bytes
  let (executingTraderQualifier, bytes) ← decodeUInt 1 bytes
  let (pad2v2, bytes) ← Alpha.decode 2 bytes
  pure ({ networkMsgId, pad2, requestHeaderComp, clOrdId, origClOrdId, securityId, price, partyIdClientId, partyIdInvestmentDecisionMaker, executingTrader, orderQty, matchInstCrossId, enrichmentRuleId, side, priceValidityCheckType, valueCheckTypeValue, valueCheckTypeQuantity, orderAttributeLiquidityProvision, timeInForce, applSeqIndicator, execInst, tradingCapacity, exDestinationType, partyIdInvestmentDecisionMakerQualifier, executingTraderQualifier, pad2v2 }, bytes)

@[simp] theorem encode_length (message : ModifyOrderSingleShortRequest) : (encode message).length = 98 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : ModifyOrderSingleShortRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : ModifyOrderSingleShortRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [RequestHeaderComp.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end ModifyOrderSingleShortRequest

/-- New Order Single Request: 202 bytes -/
structure NewOrderSingleRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  price : BitVec 64
  stopPx : BitVec 64
  volumeDiscoveryPrice : BitVec 64
  pegOffsetValueAbs : BitVec 64
  pegOffsetValuePct : BitVec 64
  clOrdId : BitVec 64
  securityId : BitVec 64
  partyIdClientId : BitVec 64
  partyIdInvestmentDecisionMaker : BitVec 64
  executingTrader : BitVec 64
  orderQty : BitVec 32
  displayQty : BitVec 32
  displayLowQty : BitVec 32
  displayHighQty : BitVec 32
  expireDate : BitVec 32
  marketSegmentId : BitVec 32
  matchInstCrossId : BitVec 32
  applSeqIndicator : BitVec 8
  side : BitVec 8
  ordType : BitVec 8
  priceValidityCheckType : BitVec 8
  valueCheckTypeValue : BitVec 8
  valueCheckTypeQuantity : BitVec 8
  orderAttributeLiquidityProvision : BitVec 8
  timeInForce : BitVec 8
  execInst : BitVec 8
  tradingSessionSubId : BitVec 8
  tradingCapacity : BitVec 8
  exDestinationType : BitVec 8
  partyIdInvestmentDecisionMakerQualifier : BitVec 8
  executingTraderQualifier : BitVec 8
  freeText1 : Alpha 12
  freeText2 : Alpha 12
  freeText4 : Alpha 16
  fixClOrdId : Alpha 20
  pad2v2 : Alpha 2
  deriving DecidableEq, Repr

namespace NewOrderSingleRequest

def encode (message : NewOrderSingleRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ Alpha.encode message.pad2
    ++ RequestHeaderComp.encode message.requestHeaderComp
    ++ encodeUIntLE 8 message.price
    ++ encodeUIntLE 8 message.stopPx
    ++ encodeUIntLE 8 message.volumeDiscoveryPrice
    ++ encodeUIntLE 8 message.pegOffsetValueAbs
    ++ encodeUIntLE 8 message.pegOffsetValuePct
    ++ encodeUIntLE 8 message.clOrdId
    ++ encodeUIntLE 8 message.securityId
    ++ encodeUIntLE 8 message.partyIdClientId
    ++ encodeUIntLE 8 message.partyIdInvestmentDecisionMaker
    ++ encodeUIntLE 8 message.executingTrader
    ++ encodeUIntLE 4 message.orderQty
    ++ encodeUIntLE 4 message.displayQty
    ++ encodeUIntLE 4 message.displayLowQty
    ++ encodeUIntLE 4 message.displayHighQty
    ++ encodeUIntLE 4 message.expireDate
    ++ encodeUIntLE 4 message.marketSegmentId
    ++ encodeUIntLE 4 message.matchInstCrossId
    ++ encodeUInt 1 message.applSeqIndicator
    ++ encodeUInt 1 message.side
    ++ encodeUInt 1 message.ordType
    ++ encodeUInt 1 message.priceValidityCheckType
    ++ encodeUInt 1 message.valueCheckTypeValue
    ++ encodeUInt 1 message.valueCheckTypeQuantity
    ++ encodeUInt 1 message.orderAttributeLiquidityProvision
    ++ encodeUInt 1 message.timeInForce
    ++ encodeUInt 1 message.execInst
    ++ encodeUInt 1 message.tradingSessionSubId
    ++ encodeUInt 1 message.tradingCapacity
    ++ encodeUInt 1 message.exDestinationType
    ++ encodeUInt 1 message.partyIdInvestmentDecisionMakerQualifier
    ++ encodeUInt 1 message.executingTraderQualifier
    ++ Alpha.encode message.freeText1
    ++ Alpha.encode message.freeText2
    ++ Alpha.encode message.freeText4
    ++ Alpha.encode message.fixClOrdId
    ++ Alpha.encode message.pad2v2

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (NewOrderSingleRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (stopPx, bytes) ← decodeUIntLE 8 bytes
  let (volumeDiscoveryPrice, bytes) ← decodeUIntLE 8 bytes
  let (pegOffsetValueAbs, bytes) ← decodeUIntLE 8 bytes
  let (pegOffsetValuePct, bytes) ← decodeUIntLE 8 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (partyIdClientId, bytes) ← decodeUIntLE 8 bytes
  let (partyIdInvestmentDecisionMaker, bytes) ← decodeUIntLE 8 bytes
  let (executingTrader, bytes) ← decodeUIntLE 8 bytes
  let (orderQty, bytes) ← decodeUIntLE 4 bytes
  let (displayQty, bytes) ← decodeUIntLE 4 bytes
  let (displayLowQty, bytes) ← decodeUIntLE 4 bytes
  let (displayHighQty, bytes) ← decodeUIntLE 4 bytes
  let (expireDate, bytes) ← decodeUIntLE 4 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (matchInstCrossId, bytes) ← decodeUIntLE 4 bytes
  let (applSeqIndicator, bytes) ← decodeUInt 1 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (ordType, bytes) ← decodeUInt 1 bytes
  let (priceValidityCheckType, bytes) ← decodeUInt 1 bytes
  let (valueCheckTypeValue, bytes) ← decodeUInt 1 bytes
  let (valueCheckTypeQuantity, bytes) ← decodeUInt 1 bytes
  let (orderAttributeLiquidityProvision, bytes) ← decodeUInt 1 bytes
  let (timeInForce, bytes) ← decodeUInt 1 bytes
  let (execInst, bytes) ← decodeUInt 1 bytes
  let (tradingSessionSubId, bytes) ← decodeUInt 1 bytes
  let (tradingCapacity, bytes) ← decodeUInt 1 bytes
  let (exDestinationType, bytes) ← decodeUInt 1 bytes
  let (partyIdInvestmentDecisionMakerQualifier, bytes) ← decodeUInt 1 bytes
  let (executingTraderQualifier, bytes) ← decodeUInt 1 bytes
  let (freeText1, bytes) ← Alpha.decode 12 bytes
  let (freeText2, bytes) ← Alpha.decode 12 bytes
  let (freeText4, bytes) ← Alpha.decode 16 bytes
  let (fixClOrdId, bytes) ← Alpha.decode 20 bytes
  let (pad2v2, bytes) ← Alpha.decode 2 bytes
  pure ({ networkMsgId, pad2, requestHeaderComp, price, stopPx, volumeDiscoveryPrice, pegOffsetValueAbs, pegOffsetValuePct, clOrdId, securityId, partyIdClientId, partyIdInvestmentDecisionMaker, executingTrader, orderQty, displayQty, displayLowQty, displayHighQty, expireDate, marketSegmentId, matchInstCrossId, applSeqIndicator, side, ordType, priceValidityCheckType, valueCheckTypeValue, valueCheckTypeQuantity, orderAttributeLiquidityProvision, timeInForce, execInst, tradingSessionSubId, tradingCapacity, exDestinationType, partyIdInvestmentDecisionMakerQualifier, executingTraderQualifier, freeText1, freeText2, freeText4, fixClOrdId, pad2v2 }, bytes)

@[simp] theorem encode_length (message : NewOrderSingleRequest) : (encode message).length = 202 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : NewOrderSingleRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : NewOrderSingleRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [RequestHeaderComp.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end NewOrderSingleRequest

/-- New Order Single Short Request: 90 bytes -/
structure NewOrderSingleShortRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  securityId : BitVec 64
  price : BitVec 64
  clOrdId : BitVec 64
  partyIdClientId : BitVec 64
  partyIdInvestmentDecisionMaker : BitVec 64
  executingTrader : BitVec 64
  orderQty : BitVec 32
  matchInstCrossId : BitVec 32
  enrichmentRuleId : BitVec 16
  side : BitVec 8
  applSeqIndicator : BitVec 8
  priceValidityCheckType : BitVec 8
  valueCheckTypeValue : BitVec 8
  valueCheckTypeQuantity : BitVec 8
  orderAttributeLiquidityProvision : BitVec 8
  timeInForce : BitVec 8
  execInst : BitVec 8
  tradingCapacity : BitVec 8
  exDestinationType : BitVec 8
  partyIdInvestmentDecisionMakerQualifier : BitVec 8
  executingTraderQualifier : BitVec 8
  pad2v2 : Alpha 2
  deriving DecidableEq, Repr

namespace NewOrderSingleShortRequest

def encode (message : NewOrderSingleShortRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ Alpha.encode message.pad2
    ++ RequestHeaderComp.encode message.requestHeaderComp
    ++ encodeUIntLE 8 message.securityId
    ++ encodeUIntLE 8 message.price
    ++ encodeUIntLE 8 message.clOrdId
    ++ encodeUIntLE 8 message.partyIdClientId
    ++ encodeUIntLE 8 message.partyIdInvestmentDecisionMaker
    ++ encodeUIntLE 8 message.executingTrader
    ++ encodeUIntLE 4 message.orderQty
    ++ encodeUIntLE 4 message.matchInstCrossId
    ++ encodeUIntLE 2 message.enrichmentRuleId
    ++ encodeUInt 1 message.side
    ++ encodeUInt 1 message.applSeqIndicator
    ++ encodeUInt 1 message.priceValidityCheckType
    ++ encodeUInt 1 message.valueCheckTypeValue
    ++ encodeUInt 1 message.valueCheckTypeQuantity
    ++ encodeUInt 1 message.orderAttributeLiquidityProvision
    ++ encodeUInt 1 message.timeInForce
    ++ encodeUInt 1 message.execInst
    ++ encodeUInt 1 message.tradingCapacity
    ++ encodeUInt 1 message.exDestinationType
    ++ encodeUInt 1 message.partyIdInvestmentDecisionMakerQualifier
    ++ encodeUInt 1 message.executingTraderQualifier
    ++ Alpha.encode message.pad2v2

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (NewOrderSingleShortRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (partyIdClientId, bytes) ← decodeUIntLE 8 bytes
  let (partyIdInvestmentDecisionMaker, bytes) ← decodeUIntLE 8 bytes
  let (executingTrader, bytes) ← decodeUIntLE 8 bytes
  let (orderQty, bytes) ← decodeUIntLE 4 bytes
  let (matchInstCrossId, bytes) ← decodeUIntLE 4 bytes
  let (enrichmentRuleId, bytes) ← decodeUIntLE 2 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (applSeqIndicator, bytes) ← decodeUInt 1 bytes
  let (priceValidityCheckType, bytes) ← decodeUInt 1 bytes
  let (valueCheckTypeValue, bytes) ← decodeUInt 1 bytes
  let (valueCheckTypeQuantity, bytes) ← decodeUInt 1 bytes
  let (orderAttributeLiquidityProvision, bytes) ← decodeUInt 1 bytes
  let (timeInForce, bytes) ← decodeUInt 1 bytes
  let (execInst, bytes) ← decodeUInt 1 bytes
  let (tradingCapacity, bytes) ← decodeUInt 1 bytes
  let (exDestinationType, bytes) ← decodeUInt 1 bytes
  let (partyIdInvestmentDecisionMakerQualifier, bytes) ← decodeUInt 1 bytes
  let (executingTraderQualifier, bytes) ← decodeUInt 1 bytes
  let (pad2v2, bytes) ← Alpha.decode 2 bytes
  pure ({ networkMsgId, pad2, requestHeaderComp, securityId, price, clOrdId, partyIdClientId, partyIdInvestmentDecisionMaker, executingTrader, orderQty, matchInstCrossId, enrichmentRuleId, side, applSeqIndicator, priceValidityCheckType, valueCheckTypeValue, valueCheckTypeQuantity, orderAttributeLiquidityProvision, timeInForce, execInst, tradingCapacity, exDestinationType, partyIdInvestmentDecisionMakerQualifier, executingTraderQualifier, pad2v2 }, bytes)

@[simp] theorem encode_length (message : NewOrderSingleShortRequest) : (encode message).length = 90 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : NewOrderSingleShortRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : NewOrderSingleShortRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [RequestHeaderComp.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end NewOrderSingleShortRequest

/-- Quote Activation Request: 50 bytes -/
structure QuoteActivationRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  partyIdInvestmentDecisionMaker : BitVec 64
  executingTrader : BitVec 64
  marketSegmentId : BitVec 32
  targetPartyIdSessionId : BitVec 32
  massActionType : BitVec 8
  partyIdInvestmentDecisionMakerQualifier : BitVec 8
  executingTraderQualifier : BitVec 8
  pad5 : Alpha 5
  deriving DecidableEq, Repr

namespace QuoteActivationRequest

def encode (message : QuoteActivationRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ Alpha.encode message.pad2
    ++ RequestHeaderComp.encode message.requestHeaderComp
    ++ encodeUIntLE 8 message.partyIdInvestmentDecisionMaker
    ++ encodeUIntLE 8 message.executingTrader
    ++ encodeUIntLE 4 message.marketSegmentId
    ++ encodeUIntLE 4 message.targetPartyIdSessionId
    ++ encodeUInt 1 message.massActionType
    ++ encodeUInt 1 message.partyIdInvestmentDecisionMakerQualifier
    ++ encodeUInt 1 message.executingTraderQualifier
    ++ Alpha.encode message.pad5

def decode (bytes : List UInt8) : Option (QuoteActivationRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (partyIdInvestmentDecisionMaker, bytes) ← decodeUIntLE 8 bytes
  let (executingTrader, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (targetPartyIdSessionId, bytes) ← decodeUIntLE 4 bytes
  let (massActionType, bytes) ← decodeUInt 1 bytes
  let (partyIdInvestmentDecisionMakerQualifier, bytes) ← decodeUInt 1 bytes
  let (executingTraderQualifier, bytes) ← decodeUInt 1 bytes
  let (pad5, bytes) ← Alpha.decode 5 bytes
  pure ({ networkMsgId, pad2, requestHeaderComp, partyIdInvestmentDecisionMaker, executingTrader, marketSegmentId, targetPartyIdSessionId, massActionType, partyIdInvestmentDecisionMakerQualifier, executingTraderQualifier, pad5 }, bytes)

@[simp] theorem encode_length (message : QuoteActivationRequest) : (encode message).length = 50 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : QuoteActivationRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : QuoteActivationRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [RequestHeaderComp.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end QuoteActivationRequest

/-- Rfq Request: 42 bytes -/
structure RfqRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  securityId : BitVec 64
  marketSegmentId : BitVec 32
  orderQty : BitVec 32
  rfqPublishIndicator : BitVec 8
  rfqRequesterDisclosureInstruction : BitVec 8
  side : BitVec 8
  pad5 : Alpha 5
  deriving DecidableEq, Repr

namespace RfqRequest

def encode (message : RfqRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ Alpha.encode message.pad2
    ++ RequestHeaderComp.encode message.requestHeaderComp
    ++ encodeUIntLE 8 message.securityId
    ++ encodeUIntLE 4 message.marketSegmentId
    ++ encodeUIntLE 4 message.orderQty
    ++ encodeUInt 1 message.rfqPublishIndicator
    ++ encodeUInt 1 message.rfqRequesterDisclosureInstruction
    ++ encodeUInt 1 message.side
    ++ Alpha.encode message.pad5

def decode (bytes : List UInt8) : Option (RfqRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (orderQty, bytes) ← decodeUIntLE 4 bytes
  let (rfqPublishIndicator, bytes) ← decodeUInt 1 bytes
  let (rfqRequesterDisclosureInstruction, bytes) ← decodeUInt 1 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (pad5, bytes) ← Alpha.decode 5 bytes
  pure ({ networkMsgId, pad2, requestHeaderComp, securityId, marketSegmentId, orderQty, rfqPublishIndicator, rfqRequesterDisclosureInstruction, side, pad5 }, bytes)

@[simp] theorem encode_length (message : RfqRequest) : (encode message).length = 42 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : RfqRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RfqRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [RequestHeaderComp.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end RfqRequest

/-- Retransmit Me Message Request: 58 bytes -/
structure RetransmitMeMessageRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  subscriptionScope : BitVec 32
  partitionId : BitVec 16
  refApplId : BitVec 8
  applBegMsgId : Alpha 16
  applEndMsgId : Alpha 16
  pad1 : Alpha 1
  deriving DecidableEq, Repr

namespace RetransmitMeMessageRequest

def encode (message : RetransmitMeMessageRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ Alpha.encode message.pad2
    ++ RequestHeaderComp.encode message.requestHeaderComp
    ++ encodeUIntLE 4 message.subscriptionScope
    ++ encodeUIntLE 2 message.partitionId
    ++ encodeUInt 1 message.refApplId
    ++ Alpha.encode message.applBegMsgId
    ++ Alpha.encode message.applEndMsgId
    ++ Alpha.encode message.pad1

def decode (bytes : List UInt8) : Option (RetransmitMeMessageRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (subscriptionScope, bytes) ← decodeUIntLE 4 bytes
  let (partitionId, bytes) ← decodeUIntLE 2 bytes
  let (refApplId, bytes) ← decodeUInt 1 bytes
  let (applBegMsgId, bytes) ← Alpha.decode 16 bytes
  let (applEndMsgId, bytes) ← Alpha.decode 16 bytes
  let (pad1, bytes) ← Alpha.decode 1 bytes
  pure ({ networkMsgId, pad2, requestHeaderComp, subscriptionScope, partitionId, refApplId, applBegMsgId, applEndMsgId, pad1 }, bytes)

@[simp] theorem encode_length (message : RetransmitMeMessageRequest) : (encode message).length = 58 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : RetransmitMeMessageRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RetransmitMeMessageRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [RequestHeaderComp.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end RetransmitMeMessageRequest

/-- Retransmit Request: 42 bytes -/
structure RetransmitRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  applBegSeqNum : BitVec 64
  applEndSeqNum : BitVec 64
  partitionId : BitVec 16
  refApplId : BitVec 8
  pad5 : Alpha 5
  deriving DecidableEq, Repr

namespace RetransmitRequest

def encode (message : RetransmitRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ Alpha.encode message.pad2
    ++ RequestHeaderComp.encode message.requestHeaderComp
    ++ encodeUIntLE 8 message.applBegSeqNum
    ++ encodeUIntLE 8 message.applEndSeqNum
    ++ encodeUIntLE 2 message.partitionId
    ++ encodeUInt 1 message.refApplId
    ++ Alpha.encode message.pad5

def decode (bytes : List UInt8) : Option (RetransmitRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (applBegSeqNum, bytes) ← decodeUIntLE 8 bytes
  let (applEndSeqNum, bytes) ← decodeUIntLE 8 bytes
  let (partitionId, bytes) ← decodeUIntLE 2 bytes
  let (refApplId, bytes) ← decodeUInt 1 bytes
  let (pad5, bytes) ← Alpha.decode 5 bytes
  pure ({ networkMsgId, pad2, requestHeaderComp, applBegSeqNum, applEndSeqNum, partitionId, refApplId, pad5 }, bytes)

@[simp] theorem encode_length (message : RetransmitRequest) : (encode message).length = 42 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : RetransmitRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RetransmitRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [RequestHeaderComp.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end RetransmitRequest

/-- Subscribe Request: 26 bytes -/
structure SubscribeRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  subscriptionScope : BitVec 32
  refApplId : BitVec 8
  pad3 : Alpha 3
  deriving DecidableEq, Repr

namespace SubscribeRequest

def encode (message : SubscribeRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ Alpha.encode message.pad2
    ++ RequestHeaderComp.encode message.requestHeaderComp
    ++ encodeUIntLE 4 message.subscriptionScope
    ++ encodeUInt 1 message.refApplId
    ++ Alpha.encode message.pad3

def decode (bytes : List UInt8) : Option (SubscribeRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (subscriptionScope, bytes) ← decodeUIntLE 4 bytes
  let (refApplId, bytes) ← decodeUInt 1 bytes
  let (pad3, bytes) ← Alpha.decode 3 bytes
  pure ({ networkMsgId, pad2, requestHeaderComp, subscriptionScope, refApplId, pad3 }, bytes)

@[simp] theorem encode_length (message : SubscribeRequest) : (encode message).length = 26 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : SubscribeRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SubscribeRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [RequestHeaderComp.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [decodeUInt_encodeUInt, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end SubscribeRequest

/-- Unsubscribe Request: 26 bytes -/
structure UnsubscribeRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  refApplSubId : BitVec 32
  pad4 : Alpha 4
  deriving DecidableEq, Repr

namespace UnsubscribeRequest

def encode (message : UnsubscribeRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ Alpha.encode message.pad2
    ++ RequestHeaderComp.encode message.requestHeaderComp
    ++ encodeUIntLE 4 message.refApplSubId
    ++ Alpha.encode message.pad4

def decode (bytes : List UInt8) : Option (UnsubscribeRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (refApplSubId, bytes) ← decodeUIntLE 4 bytes
  let (pad4, bytes) ← Alpha.decode 4 bytes
  pure ({ networkMsgId, pad2, requestHeaderComp, refApplSubId, pad4 }, bytes)

@[simp] theorem encode_length (message : UnsubscribeRequest) : (encode message).length = 26 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : UnsubscribeRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UnsubscribeRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [RequestHeaderComp.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end UnsubscribeRequest

/-- User Login Request: 58 bytes -/
structure UserLoginRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  username : BitVec 32
  password : Alpha 32
  pad4 : Alpha 4
  deriving DecidableEq, Repr

namespace UserLoginRequest

def encode (message : UserLoginRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ Alpha.encode message.pad2
    ++ RequestHeaderComp.encode message.requestHeaderComp
    ++ encodeUIntLE 4 message.username
    ++ Alpha.encode message.password
    ++ Alpha.encode message.pad4

def decode (bytes : List UInt8) : Option (UserLoginRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (username, bytes) ← decodeUIntLE 4 bytes
  let (password, bytes) ← Alpha.decode 32 bytes
  let (pad4, bytes) ← Alpha.decode 4 bytes
  pure ({ networkMsgId, pad2, requestHeaderComp, username, password, pad4 }, bytes)

@[simp] theorem encode_length (message : UserLoginRequest) : (encode message).length = 58 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : UserLoginRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UserLoginRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [RequestHeaderComp.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end UserLoginRequest

/-- User Logout Request: 26 bytes -/
structure UserLogoutRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  username : BitVec 32
  pad4 : Alpha 4
  deriving DecidableEq, Repr

namespace UserLogoutRequest

def encode (message : UserLogoutRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ Alpha.encode message.pad2
    ++ RequestHeaderComp.encode message.requestHeaderComp
    ++ encodeUIntLE 4 message.username
    ++ Alpha.encode message.pad4

def decode (bytes : List UInt8) : Option (UserLogoutRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (username, bytes) ← decodeUIntLE 4 bytes
  let (pad4, bytes) ← Alpha.decode 4 bytes
  pure ({ networkMsgId, pad2, requestHeaderComp, username, pad4 }, bytes)

@[simp] theorem encode_length (message : UserLogoutRequest) : (encode message).length = 26 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : UserLogoutRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UserLogoutRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  dsimp only
  rw [RequestHeaderComp.decode_encode, Option.bind_some]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end UserLogoutRequest

/-- Any Client Payload, selected by Template Id -/
inductive ClientPayload where
  | crossRequest (message : CrossRequest) -- 10118
  | deleteAllOrderRequest (message : DeleteAllOrderRequest) -- 10120
  | deleteAllQuoteRequest (message : DeleteAllQuoteRequest) -- 10408
  | deleteOrderSingleRequest (message : DeleteOrderSingleRequest) -- 10109
  | enterBestQuoteRequest (message : EnterBestQuoteRequest) -- 10412
  | gatewayRequest (message : GatewayRequest) -- 10020
  | heartbeat (message : Heartbeat) -- 10011
  | inquireEnrichmentRuleIdListRequest (message : InquireEnrichmentRuleIdListRequest) -- 10040
  | inquireSessionListRequest (message : InquireSessionListRequest) -- 10035
  | inquireUserRequest (message : InquireUserRequest) -- 10038
  | logonRequest (message : LogonRequest) -- 10000
  | logoutRequest (message : LogoutRequest) -- 10002
  | massQuoteRequest (message : MassQuoteRequest) -- 10405
  | modifyOrderSingleRequest (message : ModifyOrderSingleRequest) -- 10106
  | modifyOrderSingleShortRequest (message : ModifyOrderSingleShortRequest) -- 10126
  | newOrderSingleRequest (message : NewOrderSingleRequest) -- 10100
  | newOrderSingleShortRequest (message : NewOrderSingleShortRequest) -- 10125
  | quoteActivationRequest (message : QuoteActivationRequest) -- 10403
  | rfqRequest (message : RfqRequest) -- 10401
  | retransmitMeMessageRequest (message : RetransmitMeMessageRequest) -- 10026
  | retransmitRequest (message : RetransmitRequest) -- 10008
  | subscribeRequest (message : SubscribeRequest) -- 10025
  | unsubscribeRequest (message : UnsubscribeRequest) -- 10006
  | userLoginRequest (message : UserLoginRequest) -- 10018
  | userLogoutRequest (message : UserLogoutRequest) -- 10029
  deriving DecidableEq, Repr

namespace ClientPayload

/-- The Template Id each message is sent under -/
def tag : ClientPayload → BitVec 16
  | .crossRequest _ => 10118
  | .deleteAllOrderRequest _ => 10120
  | .deleteAllQuoteRequest _ => 10408
  | .deleteOrderSingleRequest _ => 10109
  | .enterBestQuoteRequest _ => 10412
  | .gatewayRequest _ => 10020
  | .heartbeat _ => 10011
  | .inquireEnrichmentRuleIdListRequest _ => 10040
  | .inquireSessionListRequest _ => 10035
  | .inquireUserRequest _ => 10038
  | .logonRequest _ => 10000
  | .logoutRequest _ => 10002
  | .massQuoteRequest _ => 10405
  | .modifyOrderSingleRequest _ => 10106
  | .modifyOrderSingleShortRequest _ => 10126
  | .newOrderSingleRequest _ => 10100
  | .newOrderSingleShortRequest _ => 10125
  | .quoteActivationRequest _ => 10403
  | .rfqRequest _ => 10401
  | .retransmitMeMessageRequest _ => 10026
  | .retransmitRequest _ => 10008
  | .subscribeRequest _ => 10025
  | .unsubscribeRequest _ => 10006
  | .userLoginRequest _ => 10018
  | .userLogoutRequest _ => 10029

def encode : ClientPayload → List UInt8
  | .crossRequest message => CrossRequest.encode message
  | .deleteAllOrderRequest message => DeleteAllOrderRequest.encode message
  | .deleteAllQuoteRequest message => DeleteAllQuoteRequest.encode message
  | .deleteOrderSingleRequest message => DeleteOrderSingleRequest.encode message
  | .enterBestQuoteRequest message => EnterBestQuoteRequest.encode message
  | .gatewayRequest message => GatewayRequest.encode message
  | .heartbeat message => Heartbeat.encode message
  | .inquireEnrichmentRuleIdListRequest message => InquireEnrichmentRuleIdListRequest.encode message
  | .inquireSessionListRequest message => InquireSessionListRequest.encode message
  | .inquireUserRequest message => InquireUserRequest.encode message
  | .logonRequest message => LogonRequest.encode message
  | .logoutRequest message => LogoutRequest.encode message
  | .massQuoteRequest message => MassQuoteRequest.encode message
  | .modifyOrderSingleRequest message => ModifyOrderSingleRequest.encode message
  | .modifyOrderSingleShortRequest message => ModifyOrderSingleShortRequest.encode message
  | .newOrderSingleRequest message => NewOrderSingleRequest.encode message
  | .newOrderSingleShortRequest message => NewOrderSingleShortRequest.encode message
  | .quoteActivationRequest message => QuoteActivationRequest.encode message
  | .rfqRequest message => RfqRequest.encode message
  | .retransmitMeMessageRequest message => RetransmitMeMessageRequest.encode message
  | .retransmitRequest message => RetransmitRequest.encode message
  | .subscribeRequest message => SubscribeRequest.encode message
  | .unsubscribeRequest message => UnsubscribeRequest.encode message
  | .userLoginRequest message => UserLoginRequest.encode message
  | .userLogoutRequest message => UserLogoutRequest.encode message

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (ClientPayload × List UInt8) :=
  if tag = 10118 then (CrossRequest.decode bytes).map fun (message, rest) => (.crossRequest message, rest)
  else if tag = 10120 then (DeleteAllOrderRequest.decode bytes).map fun (message, rest) => (.deleteAllOrderRequest message, rest)
  else if tag = 10408 then (DeleteAllQuoteRequest.decode bytes).map fun (message, rest) => (.deleteAllQuoteRequest message, rest)
  else if tag = 10109 then (DeleteOrderSingleRequest.decode bytes).map fun (message, rest) => (.deleteOrderSingleRequest message, rest)
  else if tag = 10412 then (EnterBestQuoteRequest.decode bytes).map fun (message, rest) => (.enterBestQuoteRequest message, rest)
  else if tag = 10020 then (GatewayRequest.decode bytes).map fun (message, rest) => (.gatewayRequest message, rest)
  else if tag = 10011 then (Heartbeat.decode bytes).map fun (message, rest) => (.heartbeat message, rest)
  else if tag = 10040 then (InquireEnrichmentRuleIdListRequest.decode bytes).map fun (message, rest) => (.inquireEnrichmentRuleIdListRequest message, rest)
  else if tag = 10035 then (InquireSessionListRequest.decode bytes).map fun (message, rest) => (.inquireSessionListRequest message, rest)
  else if tag = 10038 then (InquireUserRequest.decode bytes).map fun (message, rest) => (.inquireUserRequest message, rest)
  else if tag = 10000 then (LogonRequest.decode bytes).map fun (message, rest) => (.logonRequest message, rest)
  else if tag = 10002 then (LogoutRequest.decode bytes).map fun (message, rest) => (.logoutRequest message, rest)
  else if tag = 10405 then (MassQuoteRequest.decode bytes).map fun (message, rest) => (.massQuoteRequest message, rest)
  else if tag = 10106 then (ModifyOrderSingleRequest.decode bytes).map fun (message, rest) => (.modifyOrderSingleRequest message, rest)
  else if tag = 10126 then (ModifyOrderSingleShortRequest.decode bytes).map fun (message, rest) => (.modifyOrderSingleShortRequest message, rest)
  else if tag = 10100 then (NewOrderSingleRequest.decode bytes).map fun (message, rest) => (.newOrderSingleRequest message, rest)
  else if tag = 10125 then (NewOrderSingleShortRequest.decode bytes).map fun (message, rest) => (.newOrderSingleShortRequest message, rest)
  else if tag = 10403 then (QuoteActivationRequest.decode bytes).map fun (message, rest) => (.quoteActivationRequest message, rest)
  else if tag = 10401 then (RfqRequest.decode bytes).map fun (message, rest) => (.rfqRequest message, rest)
  else if tag = 10026 then (RetransmitMeMessageRequest.decode bytes).map fun (message, rest) => (.retransmitMeMessageRequest message, rest)
  else if tag = 10008 then (RetransmitRequest.decode bytes).map fun (message, rest) => (.retransmitRequest message, rest)
  else if tag = 10025 then (SubscribeRequest.decode bytes).map fun (message, rest) => (.subscribeRequest message, rest)
  else if tag = 10006 then (UnsubscribeRequest.decode bytes).map fun (message, rest) => (.unsubscribeRequest message, rest)
  else if tag = 10018 then (UserLoginRequest.decode bytes).map fun (message, rest) => (.userLoginRequest message, rest)
  else if tag = 10029 then (UserLogoutRequest.decode bytes).map fun (message, rest) => (.userLogoutRequest message, rest)
  else none

@[simp] theorem decode_encode (message : ClientPayload) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end ClientPayload

/-- Client Message -/
structure ClientMessage where
  clientPayload : ClientPayload
  deriving DecidableEq, Repr

namespace ClientMessage

def encodeBody (message : ClientMessage) : List UInt8 :=
  encodeUIntLE 2 (ClientPayload.tag message.clientPayload)
    ++ ClientPayload.encode message.clientPayload

def decodeBody (bytes : List UInt8) : Option (ClientMessage × List UInt8) := do
  let (templateId, bytes) ← decodeUIntLE 2 bytes
  let (clientPayload, bytes) ← ClientPayload.decode templateId bytes
  pure ({ clientPayload }, bytes)

theorem decodeBody_encodeBody (message : ClientMessage) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  dsimp only
  rw [ClientPayload.decode_encode, Option.bind_some]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : ClientMessage) : (encodeBody message).length + 4 < 256 ^ 4 := by
  unfold encodeBody
  cases message.clientPayload with
  | crossRequest inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length, CrossRequest.encode_length]
    omega
  | deleteAllOrderRequest inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length, DeleteAllOrderRequest.encode_length]
    omega
  | deleteAllQuoteRequest inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length, DeleteAllQuoteRequest.encode_length]
    omega
  | deleteOrderSingleRequest inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length, DeleteOrderSingleRequest.encode_length]
    omega
  | enterBestQuoteRequest inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length, EnterBestQuoteRequest.encode_length]
    omega
  | gatewayRequest inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length, GatewayRequest.encode_length]
    omega
  | heartbeat inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length, Heartbeat.encode_length]
    omega
  | inquireEnrichmentRuleIdListRequest inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length, InquireEnrichmentRuleIdListRequest.encode_length]
    omega
  | inquireSessionListRequest inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length, InquireSessionListRequest.encode_length]
    omega
  | inquireUserRequest inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length, InquireUserRequest.encode_length]
    omega
  | logonRequest inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length, LogonRequest.encode_length]
    omega
  | logoutRequest inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length, LogoutRequest.encode_length]
    omega
  | massQuoteRequest inner =>
    have bound_inner := MassQuoteRequest.encode_length_le inner
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | modifyOrderSingleRequest inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length, ModifyOrderSingleRequest.encode_length]
    omega
  | modifyOrderSingleShortRequest inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length, ModifyOrderSingleShortRequest.encode_length]
    omega
  | newOrderSingleRequest inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length, NewOrderSingleRequest.encode_length]
    omega
  | newOrderSingleShortRequest inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length, NewOrderSingleShortRequest.encode_length]
    omega
  | quoteActivationRequest inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length, QuoteActivationRequest.encode_length]
    omega
  | rfqRequest inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length, RfqRequest.encode_length]
    omega
  | retransmitMeMessageRequest inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length, RetransmitMeMessageRequest.encode_length]
    omega
  | retransmitRequest inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length, RetransmitRequest.encode_length]
    omega
  | subscribeRequest inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length, SubscribeRequest.encode_length]
    omega
  | unsubscribeRequest inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length, UnsubscribeRequest.encode_length]
    omega
  | userLoginRequest inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length, UserLoginRequest.encode_length]
    omega
  | userLogoutRequest inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length, UserLogoutRequest.encode_length]
    omega

/-- Size rule: Body Len counts the bytes after it plus 4, so it is written from the body and checked on decode -/
def encode : ClientMessage → List UInt8 :=
  encodeFramedLE 4 4 encodeBody

def decode : List UInt8 → Option (ClientMessage × List UInt8) :=
  decodeFramedLE 4 4 decodeBody

@[simp] theorem decode_encode (message : ClientMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramedLE_encodeFramedLE 4 4 encodeBody decodeBody decodeBody_encodeBody encodeBody_length_lt message rest

theorem encode_length_pos (message : ClientMessage) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramedLE_length]
  omega

end ClientMessage

/-- Client Packet -/
structure ClientPacket where
  clientMessage : List ClientMessage
  deriving DecidableEq, Repr

namespace ClientPacket

def encode (message : ClientPacket) : List UInt8 :=
  encodeMany ClientMessage.encode message.clientMessage

def decode (bytes : List UInt8) : Option ClientPacket := do
  let clientMessage ← decodeAll ClientMessage.decode bytes.length bytes
  pure { clientMessage }

theorem decode_encode (message : ClientPacket) : decode (encode message) = some message := by
  unfold decode encode
  simp only [Option.bind_eq_bind]
  rw [decodeAll_encodeMany ClientMessage.encode ClientMessage.decode ClientMessage.decode_encode ClientMessage.encode_length_pos message.clientMessage _ (encodeMany_length_ge ClientMessage.encode ClientMessage.encode_length_pos message.clientMessage), Option.bind_some]
  rfl

end ClientPacket

end Omi.EurexT7XtiFbeV61Client
