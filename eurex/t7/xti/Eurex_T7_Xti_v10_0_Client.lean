import Omi.Wire

/-!
# Eurex Exchange Cash Enhanced Trading Interface v10.0

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Approve Tes Trade Request is not framed: its length Body Len is not an integer it reads.

Note: Cross Request is not framed: its length Body Len is not an integer it reads.

Note: Delete All Order Request is not framed: its length Body Len is not an integer it reads.

Note: Delete All Quote Request is not framed: its length Body Len is not an integer it reads.

Note: Delete Order Single Request is not framed: its length Body Len is not an integer it reads.

Note: Delete Tes Trade Request is not framed: its length Body Len is not an integer it reads.

Note: Enter Tes Trade Request is not framed: its length Body Len is not an integer it reads.

Note: Heartbeat is not framed: its length Body Len is not an integer it reads.

Note: Inquire Enrichment Rule Id List Request is not framed: its length Body Len is not an integer it reads.

Note: Inquire Session List Request is not framed: its length Body Len is not an integer it reads.

Note: Inquire User Request is not framed: its length Body Len is not an integer it reads.

Note: Issuer Security State Change Request is not framed: its length Body Len is not an integer it reads.

Note: Logon Request is not framed: its length Body Len is not an integer it reads.

Note: Logout Request is not framed: its length Body Len is not an integer it reads.

Note: Mass Quote Request is not framed: its length Body Len is not an integer it reads.

Note: Modify Order Single Request is not framed: its length Body Len is not an integer it reads.

Note: Modify Order Single Short Request is not framed: its length Body Len is not an integer it reads.

Note: Modify Tes Trade Request is not framed: its length Body Len is not an integer it reads.

Note: New Order Single Request is not framed: its length Body Len is not an integer it reads.

Note: New Order Single Short Request is not framed: its length Body Len is not an integer it reads.

Note: Ping Request is not framed: its length Body Len is not an integer it reads.

Note: Quote Activation Request is not framed: its length Body Len is not an integer it reads.

Note: Rfq Request is not framed: its length Body Len is not an integer it reads.

Note: Retransmit Me Message Request is not framed: its length Body Len is not an integer it reads.

Note: Retransmit Request is not framed: its length Body Len is not an integer it reads.

Note: Single Quote Request is not framed: its length Body Len is not an integer it reads.

Note: Specialist Rfq Reject Request is not framed: its length Body Len is not an integer it reads.

Note: Specialist Rfq Reply Request is not framed: its length Body Len is not an integer it reads.

Note: Specialist Security State Change Request is not framed: its length Body Len is not an integer it reads.

Note: Subscribe Request is not framed: its length Body Len is not an integer it reads.

Note: Unsubscribe Request is not framed: its length Body Len is not an integer it reads.

Note: User Login Request is not framed: its length Body Len is not an integer it reads.

Note: User Logout Request is not framed: its length Body Len is not an integer it reads.

Note: Xetra En Light Enter Quote Request is not framed: its length Body Len is not an integer it reads.

Note: Xetra En Light Hit Quote Request is not framed: its length Body Len is not an integer it reads.

Note: Xetra En Light Open Negotiation Request is not framed: its length Body Len is not an integer it reads.

Note: Xetra En Light Quoting Status Request is not framed: its length Body Len is not an integer it reads.

Note: Xetra En Light Update Negotiation Request is not framed: its length Body Len is not an integer it reads.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.EurexT7XtiFbeV100Client

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
    ++ (encodeUIntLE 4 message.senderSubId)

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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end RequestHeaderComp

/-- Approve Tes Trade Request: 154 bytes -/
structure ApproveTesTradeRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  partyIdClientId : BitVec 64
  partyIdInvestmentDecisionMaker : BitVec 64
  executingTrader : BitVec 64
  allocQty : BitVec 64
  packageId : BitVec 32
  allocId : BitVec 32
  tesExecId : BitVec 32
  marketSegmentId : BitVec 32
  trdType : BitVec 16
  tradingCapacity : BitVec 8
  tradeReportType : BitVec 8
  side : BitVec 8
  valueCheckTypeValue : BitVec 8
  valueCheckTypeQuantity : BitVec 8
  orderAttributeLiquidityProvision : BitVec 8
  partyIdInvestmentDecisionMakerQualifier : BitVec 8
  executingTraderQualifier : BitVec 8
  orderOrigination : BitVec 8
  tradeReportId : Alpha 20
  partyExecutingFirm : Alpha 5
  partyExecutingTrader : Alpha 6
  freeText1 : Alpha 12
  freeText2 : Alpha 12
  freeText4 : Alpha 16
  pad6 : Alpha 6
  deriving DecidableEq, Repr

namespace ApproveTesTradeRequest

def encode (message : ApproveTesTradeRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 8 message.partyIdClientId
    ++ (encodeUIntLE 8 message.partyIdInvestmentDecisionMaker
    ++ (encodeUIntLE 8 message.executingTrader
    ++ (encodeUIntLE 8 message.allocQty
    ++ (encodeUIntLE 4 message.packageId
    ++ (encodeUIntLE 4 message.allocId
    ++ (encodeUIntLE 4 message.tesExecId
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 2 message.trdType
    ++ (encodeUInt 1 message.tradingCapacity
    ++ (encodeUInt 1 message.tradeReportType
    ++ (encodeUInt 1 message.side
    ++ (encodeUInt 1 message.valueCheckTypeValue
    ++ (encodeUInt 1 message.valueCheckTypeQuantity
    ++ (encodeUInt 1 message.orderAttributeLiquidityProvision
    ++ (encodeUInt 1 message.partyIdInvestmentDecisionMakerQualifier
    ++ (encodeUInt 1 message.executingTraderQualifier
    ++ (encodeUInt 1 message.orderOrigination
    ++ (Alpha.encode message.tradeReportId
    ++ (Alpha.encode message.partyExecutingFirm
    ++ (Alpha.encode message.partyExecutingTrader
    ++ (Alpha.encode message.freeText1
    ++ (Alpha.encode message.freeText2
    ++ (Alpha.encode message.freeText4
    ++ (Alpha.encode message.pad6)))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (ApproveTesTradeRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (partyIdClientId, bytes) ← decodeUIntLE 8 bytes
  let (partyIdInvestmentDecisionMaker, bytes) ← decodeUIntLE 8 bytes
  let (executingTrader, bytes) ← decodeUIntLE 8 bytes
  let (allocQty, bytes) ← decodeUIntLE 8 bytes
  let (packageId, bytes) ← decodeUIntLE 4 bytes
  let (allocId, bytes) ← decodeUIntLE 4 bytes
  let (tesExecId, bytes) ← decodeUIntLE 4 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (trdType, bytes) ← decodeUIntLE 2 bytes
  let (tradingCapacity, bytes) ← decodeUInt 1 bytes
  let (tradeReportType, bytes) ← decodeUInt 1 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (valueCheckTypeValue, bytes) ← decodeUInt 1 bytes
  let (valueCheckTypeQuantity, bytes) ← decodeUInt 1 bytes
  let (orderAttributeLiquidityProvision, bytes) ← decodeUInt 1 bytes
  let (partyIdInvestmentDecisionMakerQualifier, bytes) ← decodeUInt 1 bytes
  let (executingTraderQualifier, bytes) ← decodeUInt 1 bytes
  let (orderOrigination, bytes) ← decodeUInt 1 bytes
  let (tradeReportId, bytes) ← Alpha.decode 20 bytes
  let (partyExecutingFirm, bytes) ← Alpha.decode 5 bytes
  let (partyExecutingTrader, bytes) ← Alpha.decode 6 bytes
  let (freeText1, bytes) ← Alpha.decode 12 bytes
  let (freeText2, bytes) ← Alpha.decode 12 bytes
  let (freeText4, bytes) ← Alpha.decode 16 bytes
  let (pad6, bytes) ← Alpha.decode 6 bytes
  pure ({ networkMsgId, pad2, requestHeaderComp, partyIdClientId, partyIdInvestmentDecisionMaker, executingTrader, allocQty, packageId, allocId, tesExecId, marketSegmentId, trdType, tradingCapacity, tradeReportType, side, valueCheckTypeValue, valueCheckTypeQuantity, orderAttributeLiquidityProvision, partyIdInvestmentDecisionMakerQualifier, executingTraderQualifier, orderOrigination, tradeReportId, partyExecutingFirm, partyExecutingTrader, freeText1, freeText2, freeText4, pad6 }, bytes)

@[simp] theorem encode_length (message : ApproveTesTradeRequest) : (encode message).length = 154 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : ApproveTesTradeRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : ApproveTesTradeRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RequestHeaderComp.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ApproveTesTradeRequest

/-- Cross Request: 42 bytes -/
structure CrossRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  securityId : BitVec 64
  orderQty : BitVec 64
  marketSegmentId : BitVec 32
  pad4 : Alpha 4
  deriving DecidableEq, Repr

namespace CrossRequest

def encode (message : CrossRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.orderQty
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (Alpha.encode message.pad4))))))

def decode (bytes : List UInt8) : Option (CrossRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (orderQty, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (pad4, bytes) ← Alpha.decode 4 bytes
  pure ({ networkMsgId, pad2, requestHeaderComp, securityId, orderQty, marketSegmentId, pad4 }, bytes)

@[simp] theorem encode_length (message : CrossRequest) : (encode message).length = 42 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : CrossRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CrossRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RequestHeaderComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
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
  orderOrigination : BitVec 8
  partyIdInvestmentDecisionMakerQualifier : BitVec 8
  executingTraderQualifier : BitVec 8
  deriving DecidableEq, Repr

namespace DeleteAllOrderRequest

def encode (message : DeleteAllOrderRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 8 message.partyIdInvestmentDecisionMaker
    ++ (encodeUIntLE 8 message.executingTrader
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.targetPartyIdSessionId
    ++ (encodeUIntLE 4 message.targetPartyIdExecutingTrader
    ++ (encodeUInt 1 message.side
    ++ (encodeUInt 1 message.orderOrigination
    ++ (encodeUInt 1 message.partyIdInvestmentDecisionMakerQualifier
    ++ (encodeUInt 1 message.executingTraderQualifier)))))))))))))

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
  let (orderOrigination, bytes) ← decodeUInt 1 bytes
  let (partyIdInvestmentDecisionMakerQualifier, bytes) ← decodeUInt 1 bytes
  let (executingTraderQualifier, bytes) ← decodeUInt 1 bytes
  pure ({ networkMsgId, pad2, requestHeaderComp, securityId, price, partyIdInvestmentDecisionMaker, executingTrader, marketSegmentId, targetPartyIdSessionId, targetPartyIdExecutingTrader, side, orderOrigination, partyIdInvestmentDecisionMakerQualifier, executingTraderQualifier }, bytes)

@[simp] theorem encode_length (message : DeleteAllOrderRequest) : (encode message).length = 66 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : DeleteAllOrderRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DeleteAllOrderRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RequestHeaderComp.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
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
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 8 message.partyIdInvestmentDecisionMaker
    ++ (encodeUIntLE 8 message.executingTrader
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.targetPartyIdSessionId
    ++ (encodeUInt 1 message.partyIdInvestmentDecisionMakerQualifier
    ++ (encodeUInt 1 message.executingTraderQualifier
    ++ (Alpha.encode message.pad6)))))))))

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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RequestHeaderComp.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end DeleteAllQuoteRequest

/-- Delete Order Single Request: 114 bytes -/
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
  orderOrigination : BitVec 8
  partyIdInvestmentDecisionMakerQualifier : BitVec 8
  executingTraderQualifier : BitVec 8
  fixClOrdId : Alpha 20
  partyExecutingFirm : Alpha 5
  partyExecutingTrader : Alpha 6
  pad6 : Alpha 6
  deriving DecidableEq, Repr

namespace DeleteOrderSingleRequest

def encode (message : DeleteOrderSingleRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 8 message.origClOrdId
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.partyIdInvestmentDecisionMaker
    ++ (encodeUIntLE 8 message.executingTrader
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.targetPartyIdSessionId
    ++ (encodeUInt 1 message.orderOrigination
    ++ (encodeUInt 1 message.partyIdInvestmentDecisionMakerQualifier
    ++ (encodeUInt 1 message.executingTraderQualifier
    ++ (Alpha.encode message.fixClOrdId
    ++ (Alpha.encode message.partyExecutingFirm
    ++ (Alpha.encode message.partyExecutingTrader
    ++ (Alpha.encode message.pad6)))))))))))))))))

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
  let (orderOrigination, bytes) ← decodeUInt 1 bytes
  let (partyIdInvestmentDecisionMakerQualifier, bytes) ← decodeUInt 1 bytes
  let (executingTraderQualifier, bytes) ← decodeUInt 1 bytes
  let (fixClOrdId, bytes) ← Alpha.decode 20 bytes
  let (partyExecutingFirm, bytes) ← Alpha.decode 5 bytes
  let (partyExecutingTrader, bytes) ← Alpha.decode 6 bytes
  let (pad6, bytes) ← Alpha.decode 6 bytes
  pure ({ networkMsgId, pad2, requestHeaderComp, orderId, clOrdId, origClOrdId, securityId, partyIdInvestmentDecisionMaker, executingTrader, marketSegmentId, targetPartyIdSessionId, orderOrigination, partyIdInvestmentDecisionMakerQualifier, executingTraderQualifier, fixClOrdId, partyExecutingFirm, partyExecutingTrader, pad6 }, bytes)

@[simp] theorem encode_length (message : DeleteOrderSingleRequest) : (encode message).length = 114 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : DeleteOrderSingleRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DeleteOrderSingleRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RequestHeaderComp.decode_encode, some_bind]
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end DeleteOrderSingleRequest

/-- Delete Tes Trade Request: 58 bytes -/
structure DeleteTesTradeRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  packageId : BitVec 32
  marketSegmentId : BitVec 32
  tesExecId : BitVec 32
  trdType : BitVec 16
  tradeReportType : BitVec 8
  tradeReportId : Alpha 20
  pad5 : Alpha 5
  deriving DecidableEq, Repr

namespace DeleteTesTradeRequest

def encode (message : DeleteTesTradeRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 4 message.packageId
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.tesExecId
    ++ (encodeUIntLE 2 message.trdType
    ++ (encodeUInt 1 message.tradeReportType
    ++ (Alpha.encode message.tradeReportId
    ++ (Alpha.encode message.pad5)))))))))

def decode (bytes : List UInt8) : Option (DeleteTesTradeRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (packageId, bytes) ← decodeUIntLE 4 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (tesExecId, bytes) ← decodeUIntLE 4 bytes
  let (trdType, bytes) ← decodeUIntLE 2 bytes
  let (tradeReportType, bytes) ← decodeUInt 1 bytes
  let (tradeReportId, bytes) ← Alpha.decode 20 bytes
  let (pad5, bytes) ← Alpha.decode 5 bytes
  pure ({ networkMsgId, pad2, requestHeaderComp, packageId, marketSegmentId, tesExecId, trdType, tradeReportType, tradeReportId, pad5 }, bytes)

@[simp] theorem encode_length (message : DeleteTesTradeRequest) : (encode message).length = 58 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : DeleteTesTradeRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DeleteTesTradeRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RequestHeaderComp.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end DeleteTesTradeRequest

/-- Side Alloc Grp Comp: 32 bytes -/
structure SideAllocGrpComp where
  allocQty : BitVec 64
  individualAllocId : BitVec 32
  tesEnrichmentRuleId : BitVec 32
  side : BitVec 8
  partyExecutingFirm : Alpha 5
  partyExecutingTrader : Alpha 6
  pad4 : Alpha 4
  deriving DecidableEq, Repr

namespace SideAllocGrpComp

def encode (message : SideAllocGrpComp) : List UInt8 :=
  encodeUIntLE 8 message.allocQty
    ++ (encodeUIntLE 4 message.individualAllocId
    ++ (encodeUIntLE 4 message.tesEnrichmentRuleId
    ++ (encodeUInt 1 message.side
    ++ (Alpha.encode message.partyExecutingFirm
    ++ (Alpha.encode message.partyExecutingTrader
    ++ (Alpha.encode message.pad4))))))

def decode (bytes : List UInt8) : Option (SideAllocGrpComp × List UInt8) := do
  let (allocQty, bytes) ← decodeUIntLE 8 bytes
  let (individualAllocId, bytes) ← decodeUIntLE 4 bytes
  let (tesEnrichmentRuleId, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (partyExecutingFirm, bytes) ← Alpha.decode 5 bytes
  let (partyExecutingTrader, bytes) ← Alpha.decode 6 bytes
  let (pad4, bytes) ← Alpha.decode 4 bytes
  pure ({ allocQty, individualAllocId, tesEnrichmentRuleId, side, partyExecutingFirm, partyExecutingTrader, pad4 }, bytes)

@[simp] theorem encode_length (message : SideAllocGrpComp) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : SideAllocGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SideAllocGrpComp) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SideAllocGrpComp

/-- Enter Tes Trade Request -/
structure EnterTesTradeRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  securityId : BitVec 64
  lastPx : BitVec 64
  transBkdTime : BitVec 64
  settlCurrFxRate : BitVec 64
  marketSegmentId : BitVec 32
  settlDate : BitVec 32
  trdType : BitVec 16
  tradeReportType : BitVec 8
  tradeReportText : Alpha 20
  tradeReportId : Alpha 20
  pad4 : Alpha 4
  sideAllocGrpComp : Bounded 1 SideAllocGrpComp
  deriving DecidableEq, Repr

namespace EnterTesTradeRequest

def encode (message : EnterTesTradeRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.lastPx
    ++ (encodeUIntLE 8 message.transBkdTime
    ++ (encodeUIntLE 8 message.settlCurrFxRate
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.settlDate
    ++ (encodeUIntLE 2 message.trdType
    ++ (encodeUInt 1 message.tradeReportType
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.sideAllocGrpComp.val.length)
    ++ (Alpha.encode message.tradeReportText
    ++ (Alpha.encode message.tradeReportId
    ++ (Alpha.encode message.pad4
    ++ (encodeMany SideAllocGrpComp.encode message.sideAllocGrpComp.val)))))))))))))))

def decode (bytes : List UInt8) : Option (EnterTesTradeRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  let (transBkdTime, bytes) ← decodeUIntLE 8 bytes
  let (settlCurrFxRate, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (settlDate, bytes) ← decodeUIntLE 4 bytes
  let (trdType, bytes) ← decodeUIntLE 2 bytes
  let (tradeReportType, bytes) ← decodeUInt 1 bytes
  let (noSideAllocs, bytes) ← decodeUInt 1 bytes
  let (tradeReportText, bytes) ← Alpha.decode 20 bytes
  let (tradeReportId, bytes) ← Alpha.decode 20 bytes
  let (pad4, bytes) ← Alpha.decode 4 bytes
  let (sideAllocGrpComp_, bytes) ← decodeMany SideAllocGrpComp.decode noSideAllocs.toNat bytes
  if fits_sideAllocGrpComp : sideAllocGrpComp_.length < 256 ^ 1 then
    pure ({ networkMsgId, pad2, requestHeaderComp, securityId, lastPx, transBkdTime, settlCurrFxRate, marketSegmentId, settlDate, trdType, tradeReportType, tradeReportText, tradeReportId, pad4, sideAllocGrpComp := ⟨sideAllocGrpComp_, fits_sideAllocGrpComp⟩ }, bytes)
  else none

theorem encode_length_pos (message : EnterTesTradeRequest) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : EnterTesTradeRequest) : (encode message).length ≤ 8266 := by
  have bound_sideAllocGrpComp := message.sideAllocGrpComp.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const SideAllocGrpComp.encode 32 SideAllocGrpComp.encode_length]
  omega

@[simp] theorem decode_encode (message : EnterTesTradeRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RequestHeaderComp.decode_encode, some_bind]
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
  rw [decodeMany_bounded 1 SideAllocGrpComp.encode SideAllocGrpComp.decode SideAllocGrpComp.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.sideAllocGrpComp.length_lt]
  rfl

end EnterTesTradeRequest

/-- Heartbeat: 10 bytes -/
structure Heartbeat where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  deriving DecidableEq, Repr

namespace Heartbeat

def encode (message : Heartbeat) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ (Alpha.encode message.pad2)

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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
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
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (Alpha.encode message.lastEntityProcessed)))

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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RequestHeaderComp.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
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
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp))

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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [RequestHeaderComp.decode_encode, some_bind]
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
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (Alpha.encode message.lastEntityProcessed)))

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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RequestHeaderComp.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end InquireUserRequest

/-- Security Status Event Grp Comp: 16 bytes -/
structure SecurityStatusEventGrpComp where
  eventPx : BitVec 64
  eventDate : BitVec 32
  eventType : BitVec 8
  pad3 : Alpha 3
  deriving DecidableEq, Repr

namespace SecurityStatusEventGrpComp

def encode (message : SecurityStatusEventGrpComp) : List UInt8 :=
  encodeUIntLE 8 message.eventPx
    ++ (encodeUIntLE 4 message.eventDate
    ++ (encodeUInt 1 message.eventType
    ++ (Alpha.encode message.pad3)))

def decode (bytes : List UInt8) : Option (SecurityStatusEventGrpComp × List UInt8) := do
  let (eventPx, bytes) ← decodeUIntLE 8 bytes
  let (eventDate, bytes) ← decodeUIntLE 4 bytes
  let (eventType, bytes) ← decodeUInt 1 bytes
  let (pad3, bytes) ← Alpha.decode 3 bytes
  pure ({ eventPx, eventDate, eventType, pad3 }, bytes)

@[simp] theorem encode_length (message : SecurityStatusEventGrpComp) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : SecurityStatusEventGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SecurityStatusEventGrpComp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SecurityStatusEventGrpComp

/-- Issuer Security State Change Request -/
structure IssuerSecurityStateChangeRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  securityId : BitVec 64
  transactTime : BitVec 64
  marketSegmentId : BitVec 32
  securityStatus : BitVec 8
  soldOutIndicator : BitVec 8
  pad1 : Alpha 1
  securityStatusEventGrpComp : Bounded 1 SecurityStatusEventGrpComp
  deriving DecidableEq, Repr

namespace IssuerSecurityStateChangeRequest

def encode (message : IssuerSecurityStateChangeRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.securityStatusEventGrpComp.val.length)
    ++ (encodeUInt 1 message.securityStatus
    ++ (encodeUInt 1 message.soldOutIndicator
    ++ (Alpha.encode message.pad1
    ++ (encodeMany SecurityStatusEventGrpComp.encode message.securityStatusEventGrpComp.val))))))))))

def decode (bytes : List UInt8) : Option (IssuerSecurityStateChangeRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (noEvents, bytes) ← decodeUInt 1 bytes
  let (securityStatus, bytes) ← decodeUInt 1 bytes
  let (soldOutIndicator, bytes) ← decodeUInt 1 bytes
  let (pad1, bytes) ← Alpha.decode 1 bytes
  let (securityStatusEventGrpComp_, bytes) ← decodeMany SecurityStatusEventGrpComp.decode noEvents.toNat bytes
  if fits_securityStatusEventGrpComp : securityStatusEventGrpComp_.length < 256 ^ 1 then
    pure ({ networkMsgId, pad2, requestHeaderComp, securityId, transactTime, marketSegmentId, securityStatus, soldOutIndicator, pad1, securityStatusEventGrpComp := ⟨securityStatusEventGrpComp_, fits_securityStatusEventGrpComp⟩ }, bytes)
  else none

theorem encode_length_pos (message : IssuerSecurityStateChangeRequest) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : IssuerSecurityStateChangeRequest) : (encode message).length ≤ 4122 := by
  have bound_securityStatusEventGrpComp := message.securityStatusEventGrpComp.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const SecurityStatusEventGrpComp.encode 16 SecurityStatusEventGrpComp.encode_length]
  omega

@[simp] theorem decode_encode (message : IssuerSecurityStateChangeRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RequestHeaderComp.decode_encode, some_bind]
  dsimp only
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 SecurityStatusEventGrpComp.encode SecurityStatusEventGrpComp.decode SecurityStatusEventGrpComp.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.securityStatusEventGrpComp.length_lt]
  rfl

end IssuerSecurityStateChangeRequest

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
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 4 message.heartBtInt
    ++ (encodeUIntLE 4 message.partyIdSessionId
    ++ (Alpha.encode message.defaultCstmApplVerId
    ++ (Alpha.encode message.password
    ++ (ApplUsageOrders.encode message.applUsageOrders
    ++ (ApplUsageQuotes.encode message.applUsageQuotes
    ++ (OrderRoutingIndicator.encode message.orderRoutingIndicator
    ++ (Alpha.encode message.fixEngineName
    ++ (Alpha.encode message.fixEngineVersion
    ++ (Alpha.encode message.fixEngineVendor
    ++ (Alpha.encode message.applicationSystemName
    ++ (Alpha.encode message.applicationSystemVersion
    ++ (Alpha.encode message.applicationSystemVendor
    ++ (Alpha.encode message.pad3))))))))))))))))

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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RequestHeaderComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ApplUsageOrders.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ApplUsageQuotes.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OrderRoutingIndicator.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
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
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp))

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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [RequestHeaderComp.decode_encode, some_bind]
  rfl

end LogoutRequest

/-- Quote Entry Grp Comp: 40 bytes -/
structure QuoteEntryGrpComp where
  securityId : BitVec 64
  bidPx : BitVec 64
  bidSize : BitVec 64
  offerPx : BitVec 64
  offerSize : BitVec 64
  deriving DecidableEq, Repr

namespace QuoteEntryGrpComp

def encode (message : QuoteEntryGrpComp) : List UInt8 :=
  encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.bidPx
    ++ (encodeUIntLE 8 message.bidSize
    ++ (encodeUIntLE 8 message.offerPx
    ++ (encodeUIntLE 8 message.offerSize))))

def decode (bytes : List UInt8) : Option (QuoteEntryGrpComp × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (bidPx, bytes) ← decodeUIntLE 8 bytes
  let (bidSize, bytes) ← decodeUIntLE 8 bytes
  let (offerPx, bytes) ← decodeUIntLE 8 bytes
  let (offerSize, bytes) ← decodeUIntLE 8 bytes
  pure ({ securityId, bidPx, bidSize, offerPx, offerSize }, bytes)

@[simp] theorem encode_length (message : QuoteEntryGrpComp) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : QuoteEntryGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : QuoteEntryGrpComp) (rest : List UInt8) :
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
  quoteType : BitVec 8
  tradingCapacity : BitVec 8
  orderAttributeLiquidityProvision : BitVec 8
  partyIdInvestmentDecisionMakerQualifier : BitVec 8
  executingTraderQualifier : BitVec 8
  pad4 : Alpha 4
  quoteEntryGrpComp : Bounded 1 QuoteEntryGrpComp
  deriving DecidableEq, Repr

namespace MassQuoteRequest

def encode (message : MassQuoteRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 8 message.quoteId
    ++ (encodeUIntLE 8 message.partyIdInvestmentDecisionMaker
    ++ (encodeUIntLE 8 message.executingTrader
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.matchInstCrossId
    ++ (encodeUIntLE 2 message.enrichmentRuleId
    ++ (encodeUInt 1 message.priceValidityCheckType
    ++ (encodeUInt 1 message.valueCheckTypeValue
    ++ (encodeUInt 1 message.valueCheckTypeQuantity
    ++ (encodeUInt 1 message.quoteSizeType
    ++ (encodeUInt 1 message.quoteType
    ++ (encodeUInt 1 message.tradingCapacity
    ++ (encodeUInt 1 message.orderAttributeLiquidityProvision
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.quoteEntryGrpComp.val.length)
    ++ (encodeUInt 1 message.partyIdInvestmentDecisionMakerQualifier
    ++ (encodeUInt 1 message.executingTraderQualifier
    ++ (Alpha.encode message.pad4
    ++ (encodeMany QuoteEntryGrpComp.encode message.quoteEntryGrpComp.val))))))))))))))))))))

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
  let (quoteType, bytes) ← decodeUInt 1 bytes
  let (tradingCapacity, bytes) ← decodeUInt 1 bytes
  let (orderAttributeLiquidityProvision, bytes) ← decodeUInt 1 bytes
  let (noQuoteEntries, bytes) ← decodeUInt 1 bytes
  let (partyIdInvestmentDecisionMakerQualifier, bytes) ← decodeUInt 1 bytes
  let (executingTraderQualifier, bytes) ← decodeUInt 1 bytes
  let (pad4, bytes) ← Alpha.decode 4 bytes
  let (quoteEntryGrpComp_, bytes) ← decodeMany QuoteEntryGrpComp.decode noQuoteEntries.toNat bytes
  if fits_quoteEntryGrpComp : quoteEntryGrpComp_.length < 256 ^ 1 then
    pure ({ networkMsgId, pad2, requestHeaderComp, quoteId, partyIdInvestmentDecisionMaker, executingTrader, marketSegmentId, matchInstCrossId, enrichmentRuleId, priceValidityCheckType, valueCheckTypeValue, valueCheckTypeQuantity, quoteSizeType, quoteType, tradingCapacity, orderAttributeLiquidityProvision, partyIdInvestmentDecisionMakerQualifier, executingTraderQualifier, pad4, quoteEntryGrpComp := ⟨quoteEntryGrpComp_, fits_quoteEntryGrpComp⟩ }, bytes)
  else none

theorem encode_length_pos (message : MassQuoteRequest) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MassQuoteRequest) : (encode message).length ≤ 10266 := by
  have bound_quoteEntryGrpComp := message.quoteEntryGrpComp.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const QuoteEntryGrpComp.encode 40 QuoteEntryGrpComp.encode_length]
  omega

@[simp] theorem decode_encode (message : MassQuoteRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RequestHeaderComp.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 QuoteEntryGrpComp.encode QuoteEntryGrpComp.decode QuoteEntryGrpComp.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.quoteEntryGrpComp.length_lt]
  rfl

end MassQuoteRequest

/-- Modify Order Single Request: 250 bytes -/
structure ModifyOrderSingleRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  orderId : BitVec 64
  clOrdId : BitVec 64
  origClOrdId : BitVec 64
  securityId : BitVec 64
  price : BitVec 64
  orderQty : BitVec 64
  displayQty : BitVec 64
  displayLowQty : BitVec 64
  displayHighQty : BitVec 64
  stopPx : BitVec 64
  volumeDiscoveryPrice : BitVec 64
  pegOffsetValueAbs : BitVec 64
  pegOffsetValuePct : BitVec 64
  partyIdClientId : BitVec 64
  partyIdInvestmentDecisionMaker : BitVec 64
  executingTrader : BitVec 64
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
  orderOrigination : BitVec 8
  partyIdInvestmentDecisionMakerQualifier : BitVec 8
  executingTraderQualifier : BitVec 8
  ownershipIndicator : BitVec 8
  partyExecutingFirm : Alpha 5
  partyExecutingTrader : Alpha 6
  freeText1 : Alpha 12
  freeText2 : Alpha 12
  freeText4 : Alpha 16
  fixClOrdId : Alpha 20
  pad1 : Alpha 1
  deriving DecidableEq, Repr

namespace ModifyOrderSingleRequest

def encode (message : ModifyOrderSingleRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 8 message.origClOrdId
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 8 message.orderQty
    ++ (encodeUIntLE 8 message.displayQty
    ++ (encodeUIntLE 8 message.displayLowQty
    ++ (encodeUIntLE 8 message.displayHighQty
    ++ (encodeUIntLE 8 message.stopPx
    ++ (encodeUIntLE 8 message.volumeDiscoveryPrice
    ++ (encodeUIntLE 8 message.pegOffsetValueAbs
    ++ (encodeUIntLE 8 message.pegOffsetValuePct
    ++ (encodeUIntLE 8 message.partyIdClientId
    ++ (encodeUIntLE 8 message.partyIdInvestmentDecisionMaker
    ++ (encodeUIntLE 8 message.executingTrader
    ++ (encodeUIntLE 4 message.expireDate
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.matchInstCrossId
    ++ (encodeUIntLE 4 message.targetPartyIdSessionId
    ++ (encodeUInt 1 message.applSeqIndicator
    ++ (encodeUInt 1 message.side
    ++ (encodeUInt 1 message.ordType
    ++ (encodeUInt 1 message.priceValidityCheckType
    ++ (encodeUInt 1 message.valueCheckTypeValue
    ++ (encodeUInt 1 message.valueCheckTypeQuantity
    ++ (encodeUInt 1 message.orderAttributeLiquidityProvision
    ++ (encodeUInt 1 message.timeInForce
    ++ (encodeUInt 1 message.execInst
    ++ (encodeUInt 1 message.tradingSessionSubId
    ++ (encodeUInt 1 message.stopPxIndicator
    ++ (encodeUInt 1 message.tradingCapacity
    ++ (encodeUInt 1 message.orderOrigination
    ++ (encodeUInt 1 message.partyIdInvestmentDecisionMakerQualifier
    ++ (encodeUInt 1 message.executingTraderQualifier
    ++ (encodeUInt 1 message.ownershipIndicator
    ++ (Alpha.encode message.partyExecutingFirm
    ++ (Alpha.encode message.partyExecutingTrader
    ++ (Alpha.encode message.freeText1
    ++ (Alpha.encode message.freeText2
    ++ (Alpha.encode message.freeText4
    ++ (Alpha.encode message.fixClOrdId
    ++ (Alpha.encode message.pad1)))))))))))))))))))))))))))))))))))))))))))))

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
  let (orderQty, bytes) ← decodeUIntLE 8 bytes
  let (displayQty, bytes) ← decodeUIntLE 8 bytes
  let (displayLowQty, bytes) ← decodeUIntLE 8 bytes
  let (displayHighQty, bytes) ← decodeUIntLE 8 bytes
  let (stopPx, bytes) ← decodeUIntLE 8 bytes
  let (volumeDiscoveryPrice, bytes) ← decodeUIntLE 8 bytes
  let (pegOffsetValueAbs, bytes) ← decodeUIntLE 8 bytes
  let (pegOffsetValuePct, bytes) ← decodeUIntLE 8 bytes
  let (partyIdClientId, bytes) ← decodeUIntLE 8 bytes
  let (partyIdInvestmentDecisionMaker, bytes) ← decodeUIntLE 8 bytes
  let (executingTrader, bytes) ← decodeUIntLE 8 bytes
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
  let (orderOrigination, bytes) ← decodeUInt 1 bytes
  let (partyIdInvestmentDecisionMakerQualifier, bytes) ← decodeUInt 1 bytes
  let (executingTraderQualifier, bytes) ← decodeUInt 1 bytes
  let (ownershipIndicator, bytes) ← decodeUInt 1 bytes
  let (partyExecutingFirm, bytes) ← Alpha.decode 5 bytes
  let (partyExecutingTrader, bytes) ← Alpha.decode 6 bytes
  let (freeText1, bytes) ← Alpha.decode 12 bytes
  let (freeText2, bytes) ← Alpha.decode 12 bytes
  let (freeText4, bytes) ← Alpha.decode 16 bytes
  let (fixClOrdId, bytes) ← Alpha.decode 20 bytes
  let (pad1, bytes) ← Alpha.decode 1 bytes
  pure ({ networkMsgId, pad2, requestHeaderComp, orderId, clOrdId, origClOrdId, securityId, price, orderQty, displayQty, displayLowQty, displayHighQty, stopPx, volumeDiscoveryPrice, pegOffsetValueAbs, pegOffsetValuePct, partyIdClientId, partyIdInvestmentDecisionMaker, executingTrader, expireDate, marketSegmentId, matchInstCrossId, targetPartyIdSessionId, applSeqIndicator, side, ordType, priceValidityCheckType, valueCheckTypeValue, valueCheckTypeQuantity, orderAttributeLiquidityProvision, timeInForce, execInst, tradingSessionSubId, stopPxIndicator, tradingCapacity, orderOrigination, partyIdInvestmentDecisionMakerQualifier, executingTraderQualifier, ownershipIndicator, partyExecutingFirm, partyExecutingTrader, freeText1, freeText2, freeText4, fixClOrdId, pad1 }, bytes)

@[simp] theorem encode_length (message : ModifyOrderSingleRequest) : (encode message).length = 250 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : ModifyOrderSingleRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : ModifyOrderSingleRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RequestHeaderComp.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ModifyOrderSingleRequest

/-- Modify Order Single Short Request: 106 bytes -/
structure ModifyOrderSingleShortRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  clOrdId : BitVec 64
  origClOrdId : BitVec 64
  securityId : BitVec 64
  price : BitVec 64
  orderQty : BitVec 64
  partyIdClientId : BitVec 64
  partyIdInvestmentDecisionMaker : BitVec 64
  executingTrader : BitVec 64
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
  orderOrigination : BitVec 8
  partyIdInvestmentDecisionMakerQualifier : BitVec 8
  executingTraderQualifier : BitVec 8
  pad6 : Alpha 6
  deriving DecidableEq, Repr

namespace ModifyOrderSingleShortRequest

def encode (message : ModifyOrderSingleShortRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 8 message.origClOrdId
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 8 message.orderQty
    ++ (encodeUIntLE 8 message.partyIdClientId
    ++ (encodeUIntLE 8 message.partyIdInvestmentDecisionMaker
    ++ (encodeUIntLE 8 message.executingTrader
    ++ (encodeUIntLE 4 message.matchInstCrossId
    ++ (encodeUIntLE 2 message.enrichmentRuleId
    ++ (encodeUInt 1 message.side
    ++ (encodeUInt 1 message.priceValidityCheckType
    ++ (encodeUInt 1 message.valueCheckTypeValue
    ++ (encodeUInt 1 message.valueCheckTypeQuantity
    ++ (encodeUInt 1 message.orderAttributeLiquidityProvision
    ++ (encodeUInt 1 message.timeInForce
    ++ (encodeUInt 1 message.applSeqIndicator
    ++ (encodeUInt 1 message.execInst
    ++ (encodeUInt 1 message.tradingCapacity
    ++ (encodeUInt 1 message.orderOrigination
    ++ (encodeUInt 1 message.partyIdInvestmentDecisionMakerQualifier
    ++ (encodeUInt 1 message.executingTraderQualifier
    ++ (Alpha.encode message.pad6)))))))))))))))))))))))))

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
  let (orderQty, bytes) ← decodeUIntLE 8 bytes
  let (partyIdClientId, bytes) ← decodeUIntLE 8 bytes
  let (partyIdInvestmentDecisionMaker, bytes) ← decodeUIntLE 8 bytes
  let (executingTrader, bytes) ← decodeUIntLE 8 bytes
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
  let (orderOrigination, bytes) ← decodeUInt 1 bytes
  let (partyIdInvestmentDecisionMakerQualifier, bytes) ← decodeUInt 1 bytes
  let (executingTraderQualifier, bytes) ← decodeUInt 1 bytes
  let (pad6, bytes) ← Alpha.decode 6 bytes
  pure ({ networkMsgId, pad2, requestHeaderComp, clOrdId, origClOrdId, securityId, price, orderQty, partyIdClientId, partyIdInvestmentDecisionMaker, executingTrader, matchInstCrossId, enrichmentRuleId, side, priceValidityCheckType, valueCheckTypeValue, valueCheckTypeQuantity, orderAttributeLiquidityProvision, timeInForce, applSeqIndicator, execInst, tradingCapacity, orderOrigination, partyIdInvestmentDecisionMakerQualifier, executingTraderQualifier, pad6 }, bytes)

@[simp] theorem encode_length (message : ModifyOrderSingleShortRequest) : (encode message).length = 106 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : ModifyOrderSingleShortRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : ModifyOrderSingleShortRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RequestHeaderComp.decode_encode, some_bind]
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

end ModifyOrderSingleShortRequest

/-- Modify Tes Trade Request -/
structure ModifyTesTradeRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  lastPx : BitVec 64
  transBkdTime : BitVec 64
  marketSegmentId : BitVec 32
  packageId : BitVec 32
  tesExecId : BitVec 32
  settlDate : BitVec 32
  trdType : BitVec 16
  tradeReportType : BitVec 8
  tradeReportText : Alpha 20
  tradeReportId : Alpha 20
  pad4 : Alpha 4
  sideAllocGrpComp : Bounded 1 SideAllocGrpComp
  deriving DecidableEq, Repr

namespace ModifyTesTradeRequest

def encode (message : ModifyTesTradeRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 8 message.lastPx
    ++ (encodeUIntLE 8 message.transBkdTime
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.packageId
    ++ (encodeUIntLE 4 message.tesExecId
    ++ (encodeUIntLE 4 message.settlDate
    ++ (encodeUIntLE 2 message.trdType
    ++ (encodeUInt 1 message.tradeReportType
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.sideAllocGrpComp.val.length)
    ++ (Alpha.encode message.tradeReportText
    ++ (Alpha.encode message.tradeReportId
    ++ (Alpha.encode message.pad4
    ++ (encodeMany SideAllocGrpComp.encode message.sideAllocGrpComp.val)))))))))))))))

def decode (bytes : List UInt8) : Option (ModifyTesTradeRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  let (transBkdTime, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (packageId, bytes) ← decodeUIntLE 4 bytes
  let (tesExecId, bytes) ← decodeUIntLE 4 bytes
  let (settlDate, bytes) ← decodeUIntLE 4 bytes
  let (trdType, bytes) ← decodeUIntLE 2 bytes
  let (tradeReportType, bytes) ← decodeUInt 1 bytes
  let (noSideAllocs, bytes) ← decodeUInt 1 bytes
  let (tradeReportText, bytes) ← Alpha.decode 20 bytes
  let (tradeReportId, bytes) ← Alpha.decode 20 bytes
  let (pad4, bytes) ← Alpha.decode 4 bytes
  let (sideAllocGrpComp_, bytes) ← decodeMany SideAllocGrpComp.decode noSideAllocs.toNat bytes
  if fits_sideAllocGrpComp : sideAllocGrpComp_.length < 256 ^ 1 then
    pure ({ networkMsgId, pad2, requestHeaderComp, lastPx, transBkdTime, marketSegmentId, packageId, tesExecId, settlDate, trdType, tradeReportType, tradeReportText, tradeReportId, pad4, sideAllocGrpComp := ⟨sideAllocGrpComp_, fits_sideAllocGrpComp⟩ }, bytes)
  else none

theorem encode_length_pos (message : ModifyTesTradeRequest) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ModifyTesTradeRequest) : (encode message).length ≤ 8258 := by
  have bound_sideAllocGrpComp := message.sideAllocGrpComp.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const SideAllocGrpComp.encode 32 SideAllocGrpComp.encode_length]
  omega

@[simp] theorem decode_encode (message : ModifyTesTradeRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RequestHeaderComp.decode_encode, some_bind]
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
  rw [decodeMany_bounded 1 SideAllocGrpComp.encode SideAllocGrpComp.decode SideAllocGrpComp.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.sideAllocGrpComp.length_lt]
  rfl

end ModifyTesTradeRequest

/-- New Order Single Request: 242 bytes -/
structure NewOrderSingleRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  price : BitVec 64
  orderQty : BitVec 64
  displayQty : BitVec 64
  displayLowQty : BitVec 64
  displayHighQty : BitVec 64
  stopPx : BitVec 64
  volumeDiscoveryPrice : BitVec 64
  pegOffsetValueAbs : BitVec 64
  pegOffsetValuePct : BitVec 64
  clOrdId : BitVec 64
  securityId : BitVec 64
  partyIdClientId : BitVec 64
  partyIdInvestmentDecisionMaker : BitVec 64
  executingTrader : BitVec 64
  quoteId : BitVec 64
  expireDate : BitVec 32
  marketSegmentId : BitVec 32
  targetPartyIdSessionId : BitVec 32
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
  tradeAtCloseOptIn : BitVec 8
  tradingCapacity : BitVec 8
  orderOrigination : BitVec 8
  partyIdInvestmentDecisionMakerQualifier : BitVec 8
  executingTraderQualifier : BitVec 8
  partyExecutingFirm : Alpha 5
  partyExecutingTrader : Alpha 6
  freeText1 : Alpha 12
  freeText2 : Alpha 12
  freeText4 : Alpha 16
  fixClOrdId : Alpha 20
  pad2v2 : Alpha 2
  deriving DecidableEq, Repr

namespace NewOrderSingleRequest

def encode (message : NewOrderSingleRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 8 message.orderQty
    ++ (encodeUIntLE 8 message.displayQty
    ++ (encodeUIntLE 8 message.displayLowQty
    ++ (encodeUIntLE 8 message.displayHighQty
    ++ (encodeUIntLE 8 message.stopPx
    ++ (encodeUIntLE 8 message.volumeDiscoveryPrice
    ++ (encodeUIntLE 8 message.pegOffsetValueAbs
    ++ (encodeUIntLE 8 message.pegOffsetValuePct
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.partyIdClientId
    ++ (encodeUIntLE 8 message.partyIdInvestmentDecisionMaker
    ++ (encodeUIntLE 8 message.executingTrader
    ++ (encodeUIntLE 8 message.quoteId
    ++ (encodeUIntLE 4 message.expireDate
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.targetPartyIdSessionId
    ++ (encodeUIntLE 4 message.matchInstCrossId
    ++ (encodeUInt 1 message.applSeqIndicator
    ++ (encodeUInt 1 message.side
    ++ (encodeUInt 1 message.ordType
    ++ (encodeUInt 1 message.priceValidityCheckType
    ++ (encodeUInt 1 message.valueCheckTypeValue
    ++ (encodeUInt 1 message.valueCheckTypeQuantity
    ++ (encodeUInt 1 message.orderAttributeLiquidityProvision
    ++ (encodeUInt 1 message.timeInForce
    ++ (encodeUInt 1 message.execInst
    ++ (encodeUInt 1 message.tradingSessionSubId
    ++ (encodeUInt 1 message.tradeAtCloseOptIn
    ++ (encodeUInt 1 message.tradingCapacity
    ++ (encodeUInt 1 message.orderOrigination
    ++ (encodeUInt 1 message.partyIdInvestmentDecisionMakerQualifier
    ++ (encodeUInt 1 message.executingTraderQualifier
    ++ (Alpha.encode message.partyExecutingFirm
    ++ (Alpha.encode message.partyExecutingTrader
    ++ (Alpha.encode message.freeText1
    ++ (Alpha.encode message.freeText2
    ++ (Alpha.encode message.freeText4
    ++ (Alpha.encode message.fixClOrdId
    ++ (Alpha.encode message.pad2v2)))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (NewOrderSingleRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (orderQty, bytes) ← decodeUIntLE 8 bytes
  let (displayQty, bytes) ← decodeUIntLE 8 bytes
  let (displayLowQty, bytes) ← decodeUIntLE 8 bytes
  let (displayHighQty, bytes) ← decodeUIntLE 8 bytes
  let (stopPx, bytes) ← decodeUIntLE 8 bytes
  let (volumeDiscoveryPrice, bytes) ← decodeUIntLE 8 bytes
  let (pegOffsetValueAbs, bytes) ← decodeUIntLE 8 bytes
  let (pegOffsetValuePct, bytes) ← decodeUIntLE 8 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (partyIdClientId, bytes) ← decodeUIntLE 8 bytes
  let (partyIdInvestmentDecisionMaker, bytes) ← decodeUIntLE 8 bytes
  let (executingTrader, bytes) ← decodeUIntLE 8 bytes
  let (quoteId, bytes) ← decodeUIntLE 8 bytes
  let (expireDate, bytes) ← decodeUIntLE 4 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (targetPartyIdSessionId, bytes) ← decodeUIntLE 4 bytes
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
  let (tradeAtCloseOptIn, bytes) ← decodeUInt 1 bytes
  let (tradingCapacity, bytes) ← decodeUInt 1 bytes
  let (orderOrigination, bytes) ← decodeUInt 1 bytes
  let (partyIdInvestmentDecisionMakerQualifier, bytes) ← decodeUInt 1 bytes
  let (executingTraderQualifier, bytes) ← decodeUInt 1 bytes
  let (partyExecutingFirm, bytes) ← Alpha.decode 5 bytes
  let (partyExecutingTrader, bytes) ← Alpha.decode 6 bytes
  let (freeText1, bytes) ← Alpha.decode 12 bytes
  let (freeText2, bytes) ← Alpha.decode 12 bytes
  let (freeText4, bytes) ← Alpha.decode 16 bytes
  let (fixClOrdId, bytes) ← Alpha.decode 20 bytes
  let (pad2v2, bytes) ← Alpha.decode 2 bytes
  pure ({ networkMsgId, pad2, requestHeaderComp, price, orderQty, displayQty, displayLowQty, displayHighQty, stopPx, volumeDiscoveryPrice, pegOffsetValueAbs, pegOffsetValuePct, clOrdId, securityId, partyIdClientId, partyIdInvestmentDecisionMaker, executingTrader, quoteId, expireDate, marketSegmentId, targetPartyIdSessionId, matchInstCrossId, applSeqIndicator, side, ordType, priceValidityCheckType, valueCheckTypeValue, valueCheckTypeQuantity, orderAttributeLiquidityProvision, timeInForce, execInst, tradingSessionSubId, tradeAtCloseOptIn, tradingCapacity, orderOrigination, partyIdInvestmentDecisionMakerQualifier, executingTraderQualifier, partyExecutingFirm, partyExecutingTrader, freeText1, freeText2, freeText4, fixClOrdId, pad2v2 }, bytes)

@[simp] theorem encode_length (message : NewOrderSingleRequest) : (encode message).length = 242 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : NewOrderSingleRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : NewOrderSingleRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RequestHeaderComp.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end NewOrderSingleRequest

/-- New Order Single Short Request: 98 bytes -/
structure NewOrderSingleShortRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  securityId : BitVec 64
  price : BitVec 64
  orderQty : BitVec 64
  clOrdId : BitVec 64
  partyIdClientId : BitVec 64
  partyIdInvestmentDecisionMaker : BitVec 64
  executingTrader : BitVec 64
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
  orderOrigination : BitVec 8
  partyIdInvestmentDecisionMakerQualifier : BitVec 8
  executingTraderQualifier : BitVec 8
  pad6 : Alpha 6
  deriving DecidableEq, Repr

namespace NewOrderSingleShortRequest

def encode (message : NewOrderSingleShortRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 8 message.orderQty
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 8 message.partyIdClientId
    ++ (encodeUIntLE 8 message.partyIdInvestmentDecisionMaker
    ++ (encodeUIntLE 8 message.executingTrader
    ++ (encodeUIntLE 4 message.matchInstCrossId
    ++ (encodeUIntLE 2 message.enrichmentRuleId
    ++ (encodeUInt 1 message.side
    ++ (encodeUInt 1 message.applSeqIndicator
    ++ (encodeUInt 1 message.priceValidityCheckType
    ++ (encodeUInt 1 message.valueCheckTypeValue
    ++ (encodeUInt 1 message.valueCheckTypeQuantity
    ++ (encodeUInt 1 message.orderAttributeLiquidityProvision
    ++ (encodeUInt 1 message.timeInForce
    ++ (encodeUInt 1 message.execInst
    ++ (encodeUInt 1 message.tradingCapacity
    ++ (encodeUInt 1 message.orderOrigination
    ++ (encodeUInt 1 message.partyIdInvestmentDecisionMakerQualifier
    ++ (encodeUInt 1 message.executingTraderQualifier
    ++ (Alpha.encode message.pad6))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (NewOrderSingleShortRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (orderQty, bytes) ← decodeUIntLE 8 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (partyIdClientId, bytes) ← decodeUIntLE 8 bytes
  let (partyIdInvestmentDecisionMaker, bytes) ← decodeUIntLE 8 bytes
  let (executingTrader, bytes) ← decodeUIntLE 8 bytes
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
  let (orderOrigination, bytes) ← decodeUInt 1 bytes
  let (partyIdInvestmentDecisionMakerQualifier, bytes) ← decodeUInt 1 bytes
  let (executingTraderQualifier, bytes) ← decodeUInt 1 bytes
  let (pad6, bytes) ← Alpha.decode 6 bytes
  pure ({ networkMsgId, pad2, requestHeaderComp, securityId, price, orderQty, clOrdId, partyIdClientId, partyIdInvestmentDecisionMaker, executingTrader, matchInstCrossId, enrichmentRuleId, side, applSeqIndicator, priceValidityCheckType, valueCheckTypeValue, valueCheckTypeQuantity, orderAttributeLiquidityProvision, timeInForce, execInst, tradingCapacity, orderOrigination, partyIdInvestmentDecisionMakerQualifier, executingTraderQualifier, pad6 }, bytes)

@[simp] theorem encode_length (message : NewOrderSingleShortRequest) : (encode message).length = 98 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : NewOrderSingleShortRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : NewOrderSingleShortRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RequestHeaderComp.decode_encode, some_bind]
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

end NewOrderSingleShortRequest

/-- Ping Request: 26 bytes -/
structure PingRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  partitionId : BitVec 16
  pad6 : Alpha 6
  deriving DecidableEq, Repr

namespace PingRequest

def encode (message : PingRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 2 message.partitionId
    ++ (Alpha.encode message.pad6))))

def decode (bytes : List UInt8) : Option (PingRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (partitionId, bytes) ← decodeUIntLE 2 bytes
  let (pad6, bytes) ← Alpha.decode 6 bytes
  pure ({ networkMsgId, pad2, requestHeaderComp, partitionId, pad6 }, bytes)

@[simp] theorem encode_length (message : PingRequest) : (encode message).length = 26 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : PingRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PingRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RequestHeaderComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end PingRequest

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
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 8 message.partyIdInvestmentDecisionMaker
    ++ (encodeUIntLE 8 message.executingTrader
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.targetPartyIdSessionId
    ++ (encodeUInt 1 message.massActionType
    ++ (encodeUInt 1 message.partyIdInvestmentDecisionMakerQualifier
    ++ (encodeUInt 1 message.executingTraderQualifier
    ++ (Alpha.encode message.pad5))))))))))

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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RequestHeaderComp.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end QuoteActivationRequest

/-- Rfq Request: 50 bytes -/
structure RfqRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  securityId : BitVec 64
  orderQty : BitVec 64
  quoteId : BitVec 64
  marketSegmentId : BitVec 32
  rfqPublishIndicator : BitVec 8
  rfqRequesterDisclosureInstruction : BitVec 8
  side : BitVec 8
  pad1 : Alpha 1
  deriving DecidableEq, Repr

namespace RfqRequest

def encode (message : RfqRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.orderQty
    ++ (encodeUIntLE 8 message.quoteId
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUInt 1 message.rfqPublishIndicator
    ++ (encodeUInt 1 message.rfqRequesterDisclosureInstruction
    ++ (encodeUInt 1 message.side
    ++ (Alpha.encode message.pad1))))))))))

def decode (bytes : List UInt8) : Option (RfqRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (orderQty, bytes) ← decodeUIntLE 8 bytes
  let (quoteId, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (rfqPublishIndicator, bytes) ← decodeUInt 1 bytes
  let (rfqRequesterDisclosureInstruction, bytes) ← decodeUInt 1 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (pad1, bytes) ← Alpha.decode 1 bytes
  pure ({ networkMsgId, pad2, requestHeaderComp, securityId, orderQty, quoteId, marketSegmentId, rfqPublishIndicator, rfqRequesterDisclosureInstruction, side, pad1 }, bytes)

@[simp] theorem encode_length (message : RfqRequest) : (encode message).length = 50 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : RfqRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RfqRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RequestHeaderComp.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
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
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 4 message.subscriptionScope
    ++ (encodeUIntLE 2 message.partitionId
    ++ (encodeUInt 1 message.refApplId
    ++ (Alpha.encode message.applBegMsgId
    ++ (Alpha.encode message.applEndMsgId
    ++ (Alpha.encode message.pad1))))))))

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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RequestHeaderComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
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
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 8 message.applBegSeqNum
    ++ (encodeUIntLE 8 message.applEndSeqNum
    ++ (encodeUIntLE 2 message.partitionId
    ++ (encodeUInt 1 message.refApplId
    ++ (Alpha.encode message.pad5)))))))

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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RequestHeaderComp.decode_encode, some_bind]
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

end RetransmitRequest

/-- Single Quote Request: 154 bytes -/
structure SingleQuoteRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  quoteId : BitVec 64
  securityId : BitVec 64
  partyIdInvestmentDecisionMaker : BitVec 64
  executingTrader : BitVec 64
  bidPx : BitVec 64
  bidSize : BitVec 64
  offerPx : BitVec 64
  offerSize : BitVec 64
  settlCurrFxRate : BitVec 64
  marketSegmentId : BitVec 32
  matchInstCrossId : BitVec 32
  priceValidityCheckType : BitVec 8
  valueCheckTypeValue : BitVec 8
  valueCheckTypeQuantity : BitVec 8
  quoteSizeType : BitVec 8
  quoteType : BitVec 8
  tradingCapacity : BitVec 8
  orderAttributeLiquidityProvision : BitVec 8
  executingTraderQualifier : BitVec 8
  partyIdInvestmentDecisionMakerQualifier : BitVec 8
  freeText1 : Alpha 12
  freeText2 : Alpha 12
  freeText4 : Alpha 16
  pad7 : Alpha 7
  deriving DecidableEq, Repr

namespace SingleQuoteRequest

def encode (message : SingleQuoteRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 8 message.quoteId
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.partyIdInvestmentDecisionMaker
    ++ (encodeUIntLE 8 message.executingTrader
    ++ (encodeUIntLE 8 message.bidPx
    ++ (encodeUIntLE 8 message.bidSize
    ++ (encodeUIntLE 8 message.offerPx
    ++ (encodeUIntLE 8 message.offerSize
    ++ (encodeUIntLE 8 message.settlCurrFxRate
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.matchInstCrossId
    ++ (encodeUInt 1 message.priceValidityCheckType
    ++ (encodeUInt 1 message.valueCheckTypeValue
    ++ (encodeUInt 1 message.valueCheckTypeQuantity
    ++ (encodeUInt 1 message.quoteSizeType
    ++ (encodeUInt 1 message.quoteType
    ++ (encodeUInt 1 message.tradingCapacity
    ++ (encodeUInt 1 message.orderAttributeLiquidityProvision
    ++ (encodeUInt 1 message.executingTraderQualifier
    ++ (encodeUInt 1 message.partyIdInvestmentDecisionMakerQualifier
    ++ (Alpha.encode message.freeText1
    ++ (Alpha.encode message.freeText2
    ++ (Alpha.encode message.freeText4
    ++ (Alpha.encode message.pad7))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (SingleQuoteRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (quoteId, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (partyIdInvestmentDecisionMaker, bytes) ← decodeUIntLE 8 bytes
  let (executingTrader, bytes) ← decodeUIntLE 8 bytes
  let (bidPx, bytes) ← decodeUIntLE 8 bytes
  let (bidSize, bytes) ← decodeUIntLE 8 bytes
  let (offerPx, bytes) ← decodeUIntLE 8 bytes
  let (offerSize, bytes) ← decodeUIntLE 8 bytes
  let (settlCurrFxRate, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (matchInstCrossId, bytes) ← decodeUIntLE 4 bytes
  let (priceValidityCheckType, bytes) ← decodeUInt 1 bytes
  let (valueCheckTypeValue, bytes) ← decodeUInt 1 bytes
  let (valueCheckTypeQuantity, bytes) ← decodeUInt 1 bytes
  let (quoteSizeType, bytes) ← decodeUInt 1 bytes
  let (quoteType, bytes) ← decodeUInt 1 bytes
  let (tradingCapacity, bytes) ← decodeUInt 1 bytes
  let (orderAttributeLiquidityProvision, bytes) ← decodeUInt 1 bytes
  let (executingTraderQualifier, bytes) ← decodeUInt 1 bytes
  let (partyIdInvestmentDecisionMakerQualifier, bytes) ← decodeUInt 1 bytes
  let (freeText1, bytes) ← Alpha.decode 12 bytes
  let (freeText2, bytes) ← Alpha.decode 12 bytes
  let (freeText4, bytes) ← Alpha.decode 16 bytes
  let (pad7, bytes) ← Alpha.decode 7 bytes
  pure ({ networkMsgId, pad2, requestHeaderComp, quoteId, securityId, partyIdInvestmentDecisionMaker, executingTrader, bidPx, bidSize, offerPx, offerSize, settlCurrFxRate, marketSegmentId, matchInstCrossId, priceValidityCheckType, valueCheckTypeValue, valueCheckTypeQuantity, quoteSizeType, quoteType, tradingCapacity, orderAttributeLiquidityProvision, executingTraderQualifier, partyIdInvestmentDecisionMakerQualifier, freeText1, freeText2, freeText4, pad7 }, bytes)

@[simp] theorem encode_length (message : SingleQuoteRequest) : (encode message).length = 154 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : SingleQuoteRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : SingleQuoteRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RequestHeaderComp.decode_encode, some_bind]
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end SingleQuoteRequest

/-- Specialist Rfq Reject Request: 50 bytes -/
structure SpecialistRfqRejectRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  securityId : BitVec 64
  quoteId : BitVec 64
  marketSegmentId : BitVec 32
  quoteRequestRejectReason : BitVec 8
  partyExecutingFirm : Alpha 5
  pad6 : Alpha 6
  deriving DecidableEq, Repr

namespace SpecialistRfqRejectRequest

def encode (message : SpecialistRfqRejectRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.quoteId
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUInt 1 message.quoteRequestRejectReason
    ++ (Alpha.encode message.partyExecutingFirm
    ++ (Alpha.encode message.pad6))))))))

def decode (bytes : List UInt8) : Option (SpecialistRfqRejectRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (quoteId, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (quoteRequestRejectReason, bytes) ← decodeUInt 1 bytes
  let (partyExecutingFirm, bytes) ← Alpha.decode 5 bytes
  let (pad6, bytes) ← Alpha.decode 6 bytes
  pure ({ networkMsgId, pad2, requestHeaderComp, securityId, quoteId, marketSegmentId, quoteRequestRejectReason, partyExecutingFirm, pad6 }, bytes)

@[simp] theorem encode_length (message : SpecialistRfqRejectRequest) : (encode message).length = 50 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : SpecialistRfqRejectRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SpecialistRfqRejectRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RequestHeaderComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SpecialistRfqRejectRequest

/-- Specialist Rfq Reply Request: 82 bytes -/
structure SpecialistRfqReplyRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  securityId : BitVec 64
  quoteId : BitVec 64
  bidPx : BitVec 64
  bidSize : BitVec 64
  offerPx : BitVec 64
  offerSize : BitVec 64
  marketSegmentId : BitVec 32
  partyExecutingFirm : Alpha 5
  pad7 : Alpha 7
  deriving DecidableEq, Repr

namespace SpecialistRfqReplyRequest

def encode (message : SpecialistRfqReplyRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.quoteId
    ++ (encodeUIntLE 8 message.bidPx
    ++ (encodeUIntLE 8 message.bidSize
    ++ (encodeUIntLE 8 message.offerPx
    ++ (encodeUIntLE 8 message.offerSize
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (Alpha.encode message.partyExecutingFirm
    ++ (Alpha.encode message.pad7)))))))))))

def decode (bytes : List UInt8) : Option (SpecialistRfqReplyRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (quoteId, bytes) ← decodeUIntLE 8 bytes
  let (bidPx, bytes) ← decodeUIntLE 8 bytes
  let (bidSize, bytes) ← decodeUIntLE 8 bytes
  let (offerPx, bytes) ← decodeUIntLE 8 bytes
  let (offerSize, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (partyExecutingFirm, bytes) ← Alpha.decode 5 bytes
  let (pad7, bytes) ← Alpha.decode 7 bytes
  pure ({ networkMsgId, pad2, requestHeaderComp, securityId, quoteId, bidPx, bidSize, offerPx, offerSize, marketSegmentId, partyExecutingFirm, pad7 }, bytes)

@[simp] theorem encode_length (message : SpecialistRfqReplyRequest) : (encode message).length = 82 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : SpecialistRfqReplyRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SpecialistRfqReplyRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RequestHeaderComp.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SpecialistRfqReplyRequest

/-- Specialist Security State Change Request: 34 bytes -/
structure SpecialistSecurityStateChangeRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  securityId : BitVec 64
  marketSegmentId : BitVec 32
  eventType : BitVec 8
  pad3 : Alpha 3
  deriving DecidableEq, Repr

namespace SpecialistSecurityStateChangeRequest

def encode (message : SpecialistSecurityStateChangeRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUInt 1 message.eventType
    ++ (Alpha.encode message.pad3))))))

def decode (bytes : List UInt8) : Option (SpecialistSecurityStateChangeRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (eventType, bytes) ← decodeUInt 1 bytes
  let (pad3, bytes) ← Alpha.decode 3 bytes
  pure ({ networkMsgId, pad2, requestHeaderComp, securityId, marketSegmentId, eventType, pad3 }, bytes)

@[simp] theorem encode_length (message : SpecialistSecurityStateChangeRequest) : (encode message).length = 34 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : SpecialistSecurityStateChangeRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SpecialistSecurityStateChangeRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RequestHeaderComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SpecialistSecurityStateChangeRequest

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
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 4 message.subscriptionScope
    ++ (encodeUInt 1 message.refApplId
    ++ (Alpha.encode message.pad3)))))

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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RequestHeaderComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
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
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 4 message.refApplSubId
    ++ (Alpha.encode message.pad4))))

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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RequestHeaderComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
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
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 4 message.username
    ++ (Alpha.encode message.password
    ++ (Alpha.encode message.pad4)))))

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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RequestHeaderComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
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
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 4 message.username
    ++ (Alpha.encode message.pad4))))

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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RequestHeaderComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end UserLogoutRequest

/-- Xetra En Light Enter Quote Request: 146 bytes -/
structure XetraEnLightEnterQuoteRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  bidPx : BitVec 64
  offerPx : BitVec 64
  bidSize : BitVec 64
  offerSize : BitVec 64
  partyIdClientId : BitVec 64
  partyIdInvestmentDecisionMaker : BitVec 64
  executingTrader : BitVec 64
  marketSegmentId : BitVec 32
  negotiationId : BitVec 32
  valueCheckTypeQuantity : BitVec 8
  valueCheckTypeValue : BitVec 8
  tradingCapacity : BitVec 8
  orderAttributeLiquidityProvision : BitVec 8
  executingTraderQualifier : BitVec 8
  partyIdInvestmentDecisionMakerQualifier : BitVec 8
  partyExecutingFirm : Alpha 5
  partyExecutingTrader : Alpha 6
  freeText1 : Alpha 12
  freeText2 : Alpha 12
  freeText4 : Alpha 16
  pad7 : Alpha 7
  deriving DecidableEq, Repr

namespace XetraEnLightEnterQuoteRequest

def encode (message : XetraEnLightEnterQuoteRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 8 message.bidPx
    ++ (encodeUIntLE 8 message.offerPx
    ++ (encodeUIntLE 8 message.bidSize
    ++ (encodeUIntLE 8 message.offerSize
    ++ (encodeUIntLE 8 message.partyIdClientId
    ++ (encodeUIntLE 8 message.partyIdInvestmentDecisionMaker
    ++ (encodeUIntLE 8 message.executingTrader
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.negotiationId
    ++ (encodeUInt 1 message.valueCheckTypeQuantity
    ++ (encodeUInt 1 message.valueCheckTypeValue
    ++ (encodeUInt 1 message.tradingCapacity
    ++ (encodeUInt 1 message.orderAttributeLiquidityProvision
    ++ (encodeUInt 1 message.executingTraderQualifier
    ++ (encodeUInt 1 message.partyIdInvestmentDecisionMakerQualifier
    ++ (Alpha.encode message.partyExecutingFirm
    ++ (Alpha.encode message.partyExecutingTrader
    ++ (Alpha.encode message.freeText1
    ++ (Alpha.encode message.freeText2
    ++ (Alpha.encode message.freeText4
    ++ (Alpha.encode message.pad7)))))))))))))))))))))))

def decode (bytes : List UInt8) : Option (XetraEnLightEnterQuoteRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (bidPx, bytes) ← decodeUIntLE 8 bytes
  let (offerPx, bytes) ← decodeUIntLE 8 bytes
  let (bidSize, bytes) ← decodeUIntLE 8 bytes
  let (offerSize, bytes) ← decodeUIntLE 8 bytes
  let (partyIdClientId, bytes) ← decodeUIntLE 8 bytes
  let (partyIdInvestmentDecisionMaker, bytes) ← decodeUIntLE 8 bytes
  let (executingTrader, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (negotiationId, bytes) ← decodeUIntLE 4 bytes
  let (valueCheckTypeQuantity, bytes) ← decodeUInt 1 bytes
  let (valueCheckTypeValue, bytes) ← decodeUInt 1 bytes
  let (tradingCapacity, bytes) ← decodeUInt 1 bytes
  let (orderAttributeLiquidityProvision, bytes) ← decodeUInt 1 bytes
  let (executingTraderQualifier, bytes) ← decodeUInt 1 bytes
  let (partyIdInvestmentDecisionMakerQualifier, bytes) ← decodeUInt 1 bytes
  let (partyExecutingFirm, bytes) ← Alpha.decode 5 bytes
  let (partyExecutingTrader, bytes) ← Alpha.decode 6 bytes
  let (freeText1, bytes) ← Alpha.decode 12 bytes
  let (freeText2, bytes) ← Alpha.decode 12 bytes
  let (freeText4, bytes) ← Alpha.decode 16 bytes
  let (pad7, bytes) ← Alpha.decode 7 bytes
  pure ({ networkMsgId, pad2, requestHeaderComp, bidPx, offerPx, bidSize, offerSize, partyIdClientId, partyIdInvestmentDecisionMaker, executingTrader, marketSegmentId, negotiationId, valueCheckTypeQuantity, valueCheckTypeValue, tradingCapacity, orderAttributeLiquidityProvision, executingTraderQualifier, partyIdInvestmentDecisionMakerQualifier, partyExecutingFirm, partyExecutingTrader, freeText1, freeText2, freeText4, pad7 }, bytes)

@[simp] theorem encode_length (message : XetraEnLightEnterQuoteRequest) : (encode message).length = 146 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : XetraEnLightEnterQuoteRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : XetraEnLightEnterQuoteRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RequestHeaderComp.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end XetraEnLightEnterQuoteRequest

/-- Xetra En Light Hit Quote Request: 154 bytes -/
structure XetraEnLightHitQuoteRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  quoteId : BitVec 64
  orderQty : BitVec 64
  price : BitVec 64
  partyIdClientId : BitVec 64
  partyIdInvestmentDecisionMaker : BitVec 64
  executingTrader : BitVec 64
  marketSegmentId : BitVec 32
  negotiationId : BitVec 32
  side : BitVec 8
  valueCheckTypeQuantity : BitVec 8
  valueCheckTypeValue : BitVec 8
  tradingCapacity : BitVec 8
  orderAttributeLiquidityProvision : BitVec 8
  executingTraderQualifier : BitVec 8
  allocMethod : BitVec 8
  partyIdInvestmentDecisionMakerQualifier : BitVec 8
  orderOrigination : BitVec 8
  partyExecutingFirm : Alpha 5
  partyExecutingTrader : Alpha 6
  firmTradeId : Alpha 20
  freeText1 : Alpha 12
  freeText2 : Alpha 12
  freeText4 : Alpha 16
  deriving DecidableEq, Repr

namespace XetraEnLightHitQuoteRequest

def encode (message : XetraEnLightHitQuoteRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 8 message.quoteId
    ++ (encodeUIntLE 8 message.orderQty
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 8 message.partyIdClientId
    ++ (encodeUIntLE 8 message.partyIdInvestmentDecisionMaker
    ++ (encodeUIntLE 8 message.executingTrader
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.negotiationId
    ++ (encodeUInt 1 message.side
    ++ (encodeUInt 1 message.valueCheckTypeQuantity
    ++ (encodeUInt 1 message.valueCheckTypeValue
    ++ (encodeUInt 1 message.tradingCapacity
    ++ (encodeUInt 1 message.orderAttributeLiquidityProvision
    ++ (encodeUInt 1 message.executingTraderQualifier
    ++ (encodeUInt 1 message.allocMethod
    ++ (encodeUInt 1 message.partyIdInvestmentDecisionMakerQualifier
    ++ (encodeUInt 1 message.orderOrigination
    ++ (Alpha.encode message.partyExecutingFirm
    ++ (Alpha.encode message.partyExecutingTrader
    ++ (Alpha.encode message.firmTradeId
    ++ (Alpha.encode message.freeText1
    ++ (Alpha.encode message.freeText2
    ++ (Alpha.encode message.freeText4)))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (XetraEnLightHitQuoteRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (quoteId, bytes) ← decodeUIntLE 8 bytes
  let (orderQty, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (partyIdClientId, bytes) ← decodeUIntLE 8 bytes
  let (partyIdInvestmentDecisionMaker, bytes) ← decodeUIntLE 8 bytes
  let (executingTrader, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (negotiationId, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (valueCheckTypeQuantity, bytes) ← decodeUInt 1 bytes
  let (valueCheckTypeValue, bytes) ← decodeUInt 1 bytes
  let (tradingCapacity, bytes) ← decodeUInt 1 bytes
  let (orderAttributeLiquidityProvision, bytes) ← decodeUInt 1 bytes
  let (executingTraderQualifier, bytes) ← decodeUInt 1 bytes
  let (allocMethod, bytes) ← decodeUInt 1 bytes
  let (partyIdInvestmentDecisionMakerQualifier, bytes) ← decodeUInt 1 bytes
  let (orderOrigination, bytes) ← decodeUInt 1 bytes
  let (partyExecutingFirm, bytes) ← Alpha.decode 5 bytes
  let (partyExecutingTrader, bytes) ← Alpha.decode 6 bytes
  let (firmTradeId, bytes) ← Alpha.decode 20 bytes
  let (freeText1, bytes) ← Alpha.decode 12 bytes
  let (freeText2, bytes) ← Alpha.decode 12 bytes
  let (freeText4, bytes) ← Alpha.decode 16 bytes
  pure ({ networkMsgId, pad2, requestHeaderComp, quoteId, orderQty, price, partyIdClientId, partyIdInvestmentDecisionMaker, executingTrader, marketSegmentId, negotiationId, side, valueCheckTypeQuantity, valueCheckTypeValue, tradingCapacity, orderAttributeLiquidityProvision, executingTraderQualifier, allocMethod, partyIdInvestmentDecisionMakerQualifier, orderOrigination, partyExecutingFirm, partyExecutingTrader, firmTradeId, freeText1, freeText2, freeText4 }, bytes)

@[simp] theorem encode_length (message : XetraEnLightHitQuoteRequest) : (encode message).length = 154 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : XetraEnLightHitQuoteRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : XetraEnLightHitQuoteRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RequestHeaderComp.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end XetraEnLightHitQuoteRequest

/-- Xetra En Light Target Parties Comp: 16 bytes -/
structure XetraEnLightTargetPartiesComp where
  targetPartyIdExecutingTrader : BitVec 32
  targetPartyExecutingFirm : Alpha 5
  targetPartyExecutingTrader : Alpha 6
  pad1 : Alpha 1
  deriving DecidableEq, Repr

namespace XetraEnLightTargetPartiesComp

def encode (message : XetraEnLightTargetPartiesComp) : List UInt8 :=
  encodeUIntLE 4 message.targetPartyIdExecutingTrader
    ++ (Alpha.encode message.targetPartyExecutingFirm
    ++ (Alpha.encode message.targetPartyExecutingTrader
    ++ (Alpha.encode message.pad1)))

def decode (bytes : List UInt8) : Option (XetraEnLightTargetPartiesComp × List UInt8) := do
  let (targetPartyIdExecutingTrader, bytes) ← decodeUIntLE 4 bytes
  let (targetPartyExecutingFirm, bytes) ← Alpha.decode 5 bytes
  let (targetPartyExecutingTrader, bytes) ← Alpha.decode 6 bytes
  let (pad1, bytes) ← Alpha.decode 1 bytes
  pure ({ targetPartyIdExecutingTrader, targetPartyExecutingFirm, targetPartyExecutingTrader, pad1 }, bytes)

@[simp] theorem encode_length (message : XetraEnLightTargetPartiesComp) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : XetraEnLightTargetPartiesComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : XetraEnLightTargetPartiesComp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end XetraEnLightTargetPartiesComp

/-- Xetra En Light Open Negotiation Request -/
structure XetraEnLightOpenNegotiationRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  securityId : BitVec 64
  bidPx : BitVec 64
  offerPx : BitVec 64
  orderQty : BitVec 64
  validUntilTime : BitVec 64
  marketSegmentId : BitVec 32
  settlDate : BitVec 32
  numberOfRespDisclosureInstruction : BitVec 8
  side : BitVec 8
  valueCheckTypeValue : BitVec 8
  valueCheckTypeQuantity : BitVec 8
  respondentType : BitVec 8
  partyExecutingFirm : Alpha 5
  partyExecutingTrader : Alpha 6
  freeText5 : Alpha 132
  quoteReqId : Alpha 20
  pad7 : Alpha 7
  xetraEnLightTargetPartiesComp : Bounded 1 XetraEnLightTargetPartiesComp
  deriving DecidableEq, Repr

namespace XetraEnLightOpenNegotiationRequest

def encode (message : XetraEnLightOpenNegotiationRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.bidPx
    ++ (encodeUIntLE 8 message.offerPx
    ++ (encodeUIntLE 8 message.orderQty
    ++ (encodeUIntLE 8 message.validUntilTime
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.settlDate
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.xetraEnLightTargetPartiesComp.val.length)
    ++ (encodeUInt 1 message.numberOfRespDisclosureInstruction
    ++ (encodeUInt 1 message.side
    ++ (encodeUInt 1 message.valueCheckTypeValue
    ++ (encodeUInt 1 message.valueCheckTypeQuantity
    ++ (encodeUInt 1 message.respondentType
    ++ (Alpha.encode message.partyExecutingFirm
    ++ (Alpha.encode message.partyExecutingTrader
    ++ (Alpha.encode message.freeText5
    ++ (Alpha.encode message.quoteReqId
    ++ (Alpha.encode message.pad7
    ++ (encodeMany XetraEnLightTargetPartiesComp.encode message.xetraEnLightTargetPartiesComp.val)))))))))))))))))))))

def decode (bytes : List UInt8) : Option (XetraEnLightOpenNegotiationRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (bidPx, bytes) ← decodeUIntLE 8 bytes
  let (offerPx, bytes) ← decodeUIntLE 8 bytes
  let (orderQty, bytes) ← decodeUIntLE 8 bytes
  let (validUntilTime, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (settlDate, bytes) ← decodeUIntLE 4 bytes
  let (noTargetPartyIDs, bytes) ← decodeUInt 1 bytes
  let (numberOfRespDisclosureInstruction, bytes) ← decodeUInt 1 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (valueCheckTypeValue, bytes) ← decodeUInt 1 bytes
  let (valueCheckTypeQuantity, bytes) ← decodeUInt 1 bytes
  let (respondentType, bytes) ← decodeUInt 1 bytes
  let (partyExecutingFirm, bytes) ← Alpha.decode 5 bytes
  let (partyExecutingTrader, bytes) ← Alpha.decode 6 bytes
  let (freeText5, bytes) ← Alpha.decode 132 bytes
  let (quoteReqId, bytes) ← Alpha.decode 20 bytes
  let (pad7, bytes) ← Alpha.decode 7 bytes
  let (xetraEnLightTargetPartiesComp_, bytes) ← decodeMany XetraEnLightTargetPartiesComp.decode noTargetPartyIDs.toNat bytes
  if fits_xetraEnLightTargetPartiesComp : xetraEnLightTargetPartiesComp_.length < 256 ^ 1 then
    pure ({ networkMsgId, pad2, requestHeaderComp, securityId, bidPx, offerPx, orderQty, validUntilTime, marketSegmentId, settlDate, numberOfRespDisclosureInstruction, side, valueCheckTypeValue, valueCheckTypeQuantity, respondentType, partyExecutingFirm, partyExecutingTrader, freeText5, quoteReqId, pad7, xetraEnLightTargetPartiesComp := ⟨xetraEnLightTargetPartiesComp_, fits_xetraEnLightTargetPartiesComp⟩ }, bytes)
  else none

theorem encode_length_pos (message : XetraEnLightOpenNegotiationRequest) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : XetraEnLightOpenNegotiationRequest) : (encode message).length ≤ 4322 := by
  have bound_xetraEnLightTargetPartiesComp := message.xetraEnLightTargetPartiesComp.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const XetraEnLightTargetPartiesComp.encode 16 XetraEnLightTargetPartiesComp.encode_length]
  omega

@[simp] theorem decode_encode (message : XetraEnLightOpenNegotiationRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RequestHeaderComp.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 XetraEnLightTargetPartiesComp.encode XetraEnLightTargetPartiesComp.decode XetraEnLightTargetPartiesComp.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.xetraEnLightTargetPartiesComp.length_lt]
  rfl

end XetraEnLightOpenNegotiationRequest

/-- Xetra En Light Quoting Status Request: 42 bytes -/
structure XetraEnLightQuotingStatusRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  marketSegmentId : BitVec 32
  negotiationId : BitVec 32
  quotingStatus : BitVec 8
  partyExecutingFirm : Alpha 5
  partyExecutingTrader : Alpha 6
  pad4 : Alpha 4
  deriving DecidableEq, Repr

namespace XetraEnLightQuotingStatusRequest

def encode (message : XetraEnLightQuotingStatusRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.negotiationId
    ++ (encodeUInt 1 message.quotingStatus
    ++ (Alpha.encode message.partyExecutingFirm
    ++ (Alpha.encode message.partyExecutingTrader
    ++ (Alpha.encode message.pad4))))))))

def decode (bytes : List UInt8) : Option (XetraEnLightQuotingStatusRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (negotiationId, bytes) ← decodeUIntLE 4 bytes
  let (quotingStatus, bytes) ← decodeUInt 1 bytes
  let (partyExecutingFirm, bytes) ← Alpha.decode 5 bytes
  let (partyExecutingTrader, bytes) ← Alpha.decode 6 bytes
  let (pad4, bytes) ← Alpha.decode 4 bytes
  pure ({ networkMsgId, pad2, requestHeaderComp, marketSegmentId, negotiationId, quotingStatus, partyExecutingFirm, partyExecutingTrader, pad4 }, bytes)

@[simp] theorem encode_length (message : XetraEnLightQuotingStatusRequest) : (encode message).length = 42 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : XetraEnLightQuotingStatusRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : XetraEnLightQuotingStatusRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RequestHeaderComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end XetraEnLightQuotingStatusRequest

/-- Xetra En Light Update Negotiation Request -/
structure XetraEnLightUpdateNegotiationRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  bidPx : BitVec 64
  offerPx : BitVec 64
  orderQty : BitVec 64
  marketSegmentId : BitVec 32
  negotiationId : BitVec 32
  settlDate : BitVec 32
  numberOfRespDisclosureInstruction : BitVec 8
  side : BitVec 8
  quoteCancelType : BitVec 8
  partyExecutingFirm : Alpha 5
  partyExecutingTrader : Alpha 6
  freeText5 : Alpha 132
  pad1 : Alpha 1
  xetraEnLightTargetPartiesComp : Bounded 1 XetraEnLightTargetPartiesComp
  deriving DecidableEq, Repr

namespace XetraEnLightUpdateNegotiationRequest

def encode (message : XetraEnLightUpdateNegotiationRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 8 message.bidPx
    ++ (encodeUIntLE 8 message.offerPx
    ++ (encodeUIntLE 8 message.orderQty
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.negotiationId
    ++ (encodeUIntLE 4 message.settlDate
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.xetraEnLightTargetPartiesComp.val.length)
    ++ (encodeUInt 1 message.numberOfRespDisclosureInstruction
    ++ (encodeUInt 1 message.side
    ++ (encodeUInt 1 message.quoteCancelType
    ++ (Alpha.encode message.partyExecutingFirm
    ++ (Alpha.encode message.partyExecutingTrader
    ++ (Alpha.encode message.freeText5
    ++ (Alpha.encode message.pad1
    ++ (encodeMany XetraEnLightTargetPartiesComp.encode message.xetraEnLightTargetPartiesComp.val)))))))))))))))))

def decode (bytes : List UInt8) : Option (XetraEnLightUpdateNegotiationRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (bidPx, bytes) ← decodeUIntLE 8 bytes
  let (offerPx, bytes) ← decodeUIntLE 8 bytes
  let (orderQty, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (negotiationId, bytes) ← decodeUIntLE 4 bytes
  let (settlDate, bytes) ← decodeUIntLE 4 bytes
  let (noTargetPartyIDs, bytes) ← decodeUInt 1 bytes
  let (numberOfRespDisclosureInstruction, bytes) ← decodeUInt 1 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (quoteCancelType, bytes) ← decodeUInt 1 bytes
  let (partyExecutingFirm, bytes) ← Alpha.decode 5 bytes
  let (partyExecutingTrader, bytes) ← Alpha.decode 6 bytes
  let (freeText5, bytes) ← Alpha.decode 132 bytes
  let (pad1, bytes) ← Alpha.decode 1 bytes
  let (xetraEnLightTargetPartiesComp_, bytes) ← decodeMany XetraEnLightTargetPartiesComp.decode noTargetPartyIDs.toNat bytes
  if fits_xetraEnLightTargetPartiesComp : xetraEnLightTargetPartiesComp_.length < 256 ^ 1 then
    pure ({ networkMsgId, pad2, requestHeaderComp, bidPx, offerPx, orderQty, marketSegmentId, negotiationId, settlDate, numberOfRespDisclosureInstruction, side, quoteCancelType, partyExecutingFirm, partyExecutingTrader, freeText5, pad1, xetraEnLightTargetPartiesComp := ⟨xetraEnLightTargetPartiesComp_, fits_xetraEnLightTargetPartiesComp⟩ }, bytes)
  else none

theorem encode_length_pos (message : XetraEnLightUpdateNegotiationRequest) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : XetraEnLightUpdateNegotiationRequest) : (encode message).length ≤ 4282 := by
  have bound_xetraEnLightTargetPartiesComp := message.xetraEnLightTargetPartiesComp.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const XetraEnLightTargetPartiesComp.encode 16 XetraEnLightTargetPartiesComp.encode_length]
  omega

@[simp] theorem decode_encode (message : XetraEnLightUpdateNegotiationRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RequestHeaderComp.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 XetraEnLightTargetPartiesComp.encode XetraEnLightTargetPartiesComp.decode XetraEnLightTargetPartiesComp.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.xetraEnLightTargetPartiesComp.length_lt]
  rfl

end XetraEnLightUpdateNegotiationRequest

/-- Any Client Payload, selected by Template Id -/
inductive ClientPayload where
  | approveTesTradeRequest (message : ApproveTesTradeRequest) -- 10603
  | crossRequest (message : CrossRequest) -- 10118
  | deleteAllOrderRequest (message : DeleteAllOrderRequest) -- 10120
  | deleteAllQuoteRequest (message : DeleteAllQuoteRequest) -- 10408
  | deleteOrderSingleRequest (message : DeleteOrderSingleRequest) -- 10109
  | deleteTesTradeRequest (message : DeleteTesTradeRequest) -- 10602
  | enterTesTradeRequest (message : EnterTesTradeRequest) -- 10600
  | heartbeat (message : Heartbeat) -- 10011
  | inquireEnrichmentRuleIdListRequest (message : InquireEnrichmentRuleIdListRequest) -- 10040
  | inquireSessionListRequest (message : InquireSessionListRequest) -- 10035
  | inquireUserRequest (message : InquireUserRequest) -- 10038
  | issuerSecurityStateChangeRequest (message : IssuerSecurityStateChangeRequest) -- 10314
  | logonRequest (message : LogonRequest) -- 10000
  | logoutRequest (message : LogoutRequest) -- 10002
  | massQuoteRequest (message : MassQuoteRequest) -- 10405
  | modifyOrderSingleRequest (message : ModifyOrderSingleRequest) -- 10106
  | modifyOrderSingleShortRequest (message : ModifyOrderSingleShortRequest) -- 10126
  | modifyTesTradeRequest (message : ModifyTesTradeRequest) -- 10601
  | newOrderSingleRequest (message : NewOrderSingleRequest) -- 10100
  | newOrderSingleShortRequest (message : NewOrderSingleShortRequest) -- 10125
  | pingRequest (message : PingRequest) -- 10320
  | quoteActivationRequest (message : QuoteActivationRequest) -- 10403
  | rfqRequest (message : RfqRequest) -- 10401
  | retransmitMeMessageRequest (message : RetransmitMeMessageRequest) -- 10026
  | retransmitRequest (message : RetransmitRequest) -- 10008
  | singleQuoteRequest (message : SingleQuoteRequest) -- 10418
  | specialistRfqRejectRequest (message : SpecialistRfqRejectRequest) -- 10421
  | specialistRfqReplyRequest (message : SpecialistRfqReplyRequest) -- 10422
  | specialistSecurityStateChangeRequest (message : SpecialistSecurityStateChangeRequest) -- 10317
  | subscribeRequest (message : SubscribeRequest) -- 10025
  | unsubscribeRequest (message : UnsubscribeRequest) -- 10006
  | userLoginRequest (message : UserLoginRequest) -- 10018
  | userLogoutRequest (message : UserLogoutRequest) -- 10029
  | xetraEnLightEnterQuoteRequest (message : XetraEnLightEnterQuoteRequest) -- 10802
  | xetraEnLightHitQuoteRequest (message : XetraEnLightHitQuoteRequest) -- 10804
  | xetraEnLightOpenNegotiationRequest (message : XetraEnLightOpenNegotiationRequest) -- 10800
  | xetraEnLightQuotingStatusRequest (message : XetraEnLightQuotingStatusRequest) -- 10817
  | xetraEnLightUpdateNegotiationRequest (message : XetraEnLightUpdateNegotiationRequest) -- 10801
  deriving DecidableEq, Repr

namespace ClientPayload

/-- The Template Id each message is sent under -/
def tag : ClientPayload → BitVec 16
  | .approveTesTradeRequest _ => 10603
  | .crossRequest _ => 10118
  | .deleteAllOrderRequest _ => 10120
  | .deleteAllQuoteRequest _ => 10408
  | .deleteOrderSingleRequest _ => 10109
  | .deleteTesTradeRequest _ => 10602
  | .enterTesTradeRequest _ => 10600
  | .heartbeat _ => 10011
  | .inquireEnrichmentRuleIdListRequest _ => 10040
  | .inquireSessionListRequest _ => 10035
  | .inquireUserRequest _ => 10038
  | .issuerSecurityStateChangeRequest _ => 10314
  | .logonRequest _ => 10000
  | .logoutRequest _ => 10002
  | .massQuoteRequest _ => 10405
  | .modifyOrderSingleRequest _ => 10106
  | .modifyOrderSingleShortRequest _ => 10126
  | .modifyTesTradeRequest _ => 10601
  | .newOrderSingleRequest _ => 10100
  | .newOrderSingleShortRequest _ => 10125
  | .pingRequest _ => 10320
  | .quoteActivationRequest _ => 10403
  | .rfqRequest _ => 10401
  | .retransmitMeMessageRequest _ => 10026
  | .retransmitRequest _ => 10008
  | .singleQuoteRequest _ => 10418
  | .specialistRfqRejectRequest _ => 10421
  | .specialistRfqReplyRequest _ => 10422
  | .specialistSecurityStateChangeRequest _ => 10317
  | .subscribeRequest _ => 10025
  | .unsubscribeRequest _ => 10006
  | .userLoginRequest _ => 10018
  | .userLogoutRequest _ => 10029
  | .xetraEnLightEnterQuoteRequest _ => 10802
  | .xetraEnLightHitQuoteRequest _ => 10804
  | .xetraEnLightOpenNegotiationRequest _ => 10800
  | .xetraEnLightQuotingStatusRequest _ => 10817
  | .xetraEnLightUpdateNegotiationRequest _ => 10801

def encode : ClientPayload → List UInt8
  | .approveTesTradeRequest message => ApproveTesTradeRequest.encode message
  | .crossRequest message => CrossRequest.encode message
  | .deleteAllOrderRequest message => DeleteAllOrderRequest.encode message
  | .deleteAllQuoteRequest message => DeleteAllQuoteRequest.encode message
  | .deleteOrderSingleRequest message => DeleteOrderSingleRequest.encode message
  | .deleteTesTradeRequest message => DeleteTesTradeRequest.encode message
  | .enterTesTradeRequest message => EnterTesTradeRequest.encode message
  | .heartbeat message => Heartbeat.encode message
  | .inquireEnrichmentRuleIdListRequest message => InquireEnrichmentRuleIdListRequest.encode message
  | .inquireSessionListRequest message => InquireSessionListRequest.encode message
  | .inquireUserRequest message => InquireUserRequest.encode message
  | .issuerSecurityStateChangeRequest message => IssuerSecurityStateChangeRequest.encode message
  | .logonRequest message => LogonRequest.encode message
  | .logoutRequest message => LogoutRequest.encode message
  | .massQuoteRequest message => MassQuoteRequest.encode message
  | .modifyOrderSingleRequest message => ModifyOrderSingleRequest.encode message
  | .modifyOrderSingleShortRequest message => ModifyOrderSingleShortRequest.encode message
  | .modifyTesTradeRequest message => ModifyTesTradeRequest.encode message
  | .newOrderSingleRequest message => NewOrderSingleRequest.encode message
  | .newOrderSingleShortRequest message => NewOrderSingleShortRequest.encode message
  | .pingRequest message => PingRequest.encode message
  | .quoteActivationRequest message => QuoteActivationRequest.encode message
  | .rfqRequest message => RfqRequest.encode message
  | .retransmitMeMessageRequest message => RetransmitMeMessageRequest.encode message
  | .retransmitRequest message => RetransmitRequest.encode message
  | .singleQuoteRequest message => SingleQuoteRequest.encode message
  | .specialistRfqRejectRequest message => SpecialistRfqRejectRequest.encode message
  | .specialistRfqReplyRequest message => SpecialistRfqReplyRequest.encode message
  | .specialistSecurityStateChangeRequest message => SpecialistSecurityStateChangeRequest.encode message
  | .subscribeRequest message => SubscribeRequest.encode message
  | .unsubscribeRequest message => UnsubscribeRequest.encode message
  | .userLoginRequest message => UserLoginRequest.encode message
  | .userLogoutRequest message => UserLogoutRequest.encode message
  | .xetraEnLightEnterQuoteRequest message => XetraEnLightEnterQuoteRequest.encode message
  | .xetraEnLightHitQuoteRequest message => XetraEnLightHitQuoteRequest.encode message
  | .xetraEnLightOpenNegotiationRequest message => XetraEnLightOpenNegotiationRequest.encode message
  | .xetraEnLightQuotingStatusRequest message => XetraEnLightQuotingStatusRequest.encode message
  | .xetraEnLightUpdateNegotiationRequest message => XetraEnLightUpdateNegotiationRequest.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : ClientPayload) : (encode message).length ≤ 10266 := by
  cases message with
  | approveTesTradeRequest inner =>
    simp only [encode, ApproveTesTradeRequest.encode_length]
    omega
  | crossRequest inner =>
    simp only [encode, CrossRequest.encode_length]
    omega
  | deleteAllOrderRequest inner =>
    simp only [encode, DeleteAllOrderRequest.encode_length]
    omega
  | deleteAllQuoteRequest inner =>
    simp only [encode, DeleteAllQuoteRequest.encode_length]
    omega
  | deleteOrderSingleRequest inner =>
    simp only [encode, DeleteOrderSingleRequest.encode_length]
    omega
  | deleteTesTradeRequest inner =>
    simp only [encode, DeleteTesTradeRequest.encode_length]
    omega
  | enterTesTradeRequest inner =>
    have bound_inner := EnterTesTradeRequest.encode_length_le inner
    simp only [encode]
    omega
  | heartbeat inner =>
    simp only [encode, Heartbeat.encode_length]
    omega
  | inquireEnrichmentRuleIdListRequest inner =>
    simp only [encode, InquireEnrichmentRuleIdListRequest.encode_length]
    omega
  | inquireSessionListRequest inner =>
    simp only [encode, InquireSessionListRequest.encode_length]
    omega
  | inquireUserRequest inner =>
    simp only [encode, InquireUserRequest.encode_length]
    omega
  | issuerSecurityStateChangeRequest inner =>
    have bound_inner := IssuerSecurityStateChangeRequest.encode_length_le inner
    simp only [encode]
    omega
  | logonRequest inner =>
    simp only [encode, LogonRequest.encode_length]
    omega
  | logoutRequest inner =>
    simp only [encode, LogoutRequest.encode_length]
    omega
  | massQuoteRequest inner =>
    have bound_inner := MassQuoteRequest.encode_length_le inner
    simp only [encode]
    omega
  | modifyOrderSingleRequest inner =>
    simp only [encode, ModifyOrderSingleRequest.encode_length]
    omega
  | modifyOrderSingleShortRequest inner =>
    simp only [encode, ModifyOrderSingleShortRequest.encode_length]
    omega
  | modifyTesTradeRequest inner =>
    have bound_inner := ModifyTesTradeRequest.encode_length_le inner
    simp only [encode]
    omega
  | newOrderSingleRequest inner =>
    simp only [encode, NewOrderSingleRequest.encode_length]
    omega
  | newOrderSingleShortRequest inner =>
    simp only [encode, NewOrderSingleShortRequest.encode_length]
    omega
  | pingRequest inner =>
    simp only [encode, PingRequest.encode_length]
    omega
  | quoteActivationRequest inner =>
    simp only [encode, QuoteActivationRequest.encode_length]
    omega
  | rfqRequest inner =>
    simp only [encode, RfqRequest.encode_length]
    omega
  | retransmitMeMessageRequest inner =>
    simp only [encode, RetransmitMeMessageRequest.encode_length]
    omega
  | retransmitRequest inner =>
    simp only [encode, RetransmitRequest.encode_length]
    omega
  | singleQuoteRequest inner =>
    simp only [encode, SingleQuoteRequest.encode_length]
    omega
  | specialistRfqRejectRequest inner =>
    simp only [encode, SpecialistRfqRejectRequest.encode_length]
    omega
  | specialistRfqReplyRequest inner =>
    simp only [encode, SpecialistRfqReplyRequest.encode_length]
    omega
  | specialistSecurityStateChangeRequest inner =>
    simp only [encode, SpecialistSecurityStateChangeRequest.encode_length]
    omega
  | subscribeRequest inner =>
    simp only [encode, SubscribeRequest.encode_length]
    omega
  | unsubscribeRequest inner =>
    simp only [encode, UnsubscribeRequest.encode_length]
    omega
  | userLoginRequest inner =>
    simp only [encode, UserLoginRequest.encode_length]
    omega
  | userLogoutRequest inner =>
    simp only [encode, UserLogoutRequest.encode_length]
    omega
  | xetraEnLightEnterQuoteRequest inner =>
    simp only [encode, XetraEnLightEnterQuoteRequest.encode_length]
    omega
  | xetraEnLightHitQuoteRequest inner =>
    simp only [encode, XetraEnLightHitQuoteRequest.encode_length]
    omega
  | xetraEnLightOpenNegotiationRequest inner =>
    have bound_inner := XetraEnLightOpenNegotiationRequest.encode_length_le inner
    simp only [encode]
    omega
  | xetraEnLightQuotingStatusRequest inner =>
    simp only [encode, XetraEnLightQuotingStatusRequest.encode_length]
    omega
  | xetraEnLightUpdateNegotiationRequest inner =>
    have bound_inner := XetraEnLightUpdateNegotiationRequest.encode_length_le inner
    simp only [encode]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (ClientPayload × List UInt8) :=
  if tag = 10603 then (ApproveTesTradeRequest.decode bytes).map fun (message, rest) => (.approveTesTradeRequest message, rest)
  else if tag = 10118 then (CrossRequest.decode bytes).map fun (message, rest) => (.crossRequest message, rest)
  else if tag = 10120 then (DeleteAllOrderRequest.decode bytes).map fun (message, rest) => (.deleteAllOrderRequest message, rest)
  else if tag = 10408 then (DeleteAllQuoteRequest.decode bytes).map fun (message, rest) => (.deleteAllQuoteRequest message, rest)
  else if tag = 10109 then (DeleteOrderSingleRequest.decode bytes).map fun (message, rest) => (.deleteOrderSingleRequest message, rest)
  else if tag = 10602 then (DeleteTesTradeRequest.decode bytes).map fun (message, rest) => (.deleteTesTradeRequest message, rest)
  else if tag = 10600 then (EnterTesTradeRequest.decode bytes).map fun (message, rest) => (.enterTesTradeRequest message, rest)
  else if tag = 10011 then (Heartbeat.decode bytes).map fun (message, rest) => (.heartbeat message, rest)
  else if tag = 10040 then (InquireEnrichmentRuleIdListRequest.decode bytes).map fun (message, rest) => (.inquireEnrichmentRuleIdListRequest message, rest)
  else if tag = 10035 then (InquireSessionListRequest.decode bytes).map fun (message, rest) => (.inquireSessionListRequest message, rest)
  else if tag = 10038 then (InquireUserRequest.decode bytes).map fun (message, rest) => (.inquireUserRequest message, rest)
  else if tag = 10314 then (IssuerSecurityStateChangeRequest.decode bytes).map fun (message, rest) => (.issuerSecurityStateChangeRequest message, rest)
  else if tag = 10000 then (LogonRequest.decode bytes).map fun (message, rest) => (.logonRequest message, rest)
  else if tag = 10002 then (LogoutRequest.decode bytes).map fun (message, rest) => (.logoutRequest message, rest)
  else if tag = 10405 then (MassQuoteRequest.decode bytes).map fun (message, rest) => (.massQuoteRequest message, rest)
  else if tag = 10106 then (ModifyOrderSingleRequest.decode bytes).map fun (message, rest) => (.modifyOrderSingleRequest message, rest)
  else if tag = 10126 then (ModifyOrderSingleShortRequest.decode bytes).map fun (message, rest) => (.modifyOrderSingleShortRequest message, rest)
  else if tag = 10601 then (ModifyTesTradeRequest.decode bytes).map fun (message, rest) => (.modifyTesTradeRequest message, rest)
  else if tag = 10100 then (NewOrderSingleRequest.decode bytes).map fun (message, rest) => (.newOrderSingleRequest message, rest)
  else if tag = 10125 then (NewOrderSingleShortRequest.decode bytes).map fun (message, rest) => (.newOrderSingleShortRequest message, rest)
  else if tag = 10320 then (PingRequest.decode bytes).map fun (message, rest) => (.pingRequest message, rest)
  else if tag = 10403 then (QuoteActivationRequest.decode bytes).map fun (message, rest) => (.quoteActivationRequest message, rest)
  else if tag = 10401 then (RfqRequest.decode bytes).map fun (message, rest) => (.rfqRequest message, rest)
  else if tag = 10026 then (RetransmitMeMessageRequest.decode bytes).map fun (message, rest) => (.retransmitMeMessageRequest message, rest)
  else if tag = 10008 then (RetransmitRequest.decode bytes).map fun (message, rest) => (.retransmitRequest message, rest)
  else if tag = 10418 then (SingleQuoteRequest.decode bytes).map fun (message, rest) => (.singleQuoteRequest message, rest)
  else if tag = 10421 then (SpecialistRfqRejectRequest.decode bytes).map fun (message, rest) => (.specialistRfqRejectRequest message, rest)
  else if tag = 10422 then (SpecialistRfqReplyRequest.decode bytes).map fun (message, rest) => (.specialistRfqReplyRequest message, rest)
  else if tag = 10317 then (SpecialistSecurityStateChangeRequest.decode bytes).map fun (message, rest) => (.specialistSecurityStateChangeRequest message, rest)
  else if tag = 10025 then (SubscribeRequest.decode bytes).map fun (message, rest) => (.subscribeRequest message, rest)
  else if tag = 10006 then (UnsubscribeRequest.decode bytes).map fun (message, rest) => (.unsubscribeRequest message, rest)
  else if tag = 10018 then (UserLoginRequest.decode bytes).map fun (message, rest) => (.userLoginRequest message, rest)
  else if tag = 10029 then (UserLogoutRequest.decode bytes).map fun (message, rest) => (.userLogoutRequest message, rest)
  else if tag = 10802 then (XetraEnLightEnterQuoteRequest.decode bytes).map fun (message, rest) => (.xetraEnLightEnterQuoteRequest message, rest)
  else if tag = 10804 then (XetraEnLightHitQuoteRequest.decode bytes).map fun (message, rest) => (.xetraEnLightHitQuoteRequest message, rest)
  else if tag = 10800 then (XetraEnLightOpenNegotiationRequest.decode bytes).map fun (message, rest) => (.xetraEnLightOpenNegotiationRequest message, rest)
  else if tag = 10817 then (XetraEnLightQuotingStatusRequest.decode bytes).map fun (message, rest) => (.xetraEnLightQuotingStatusRequest message, rest)
  else if tag = 10801 then (XetraEnLightUpdateNegotiationRequest.decode bytes).map fun (message, rest) => (.xetraEnLightUpdateNegotiationRequest message, rest)
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
    ++ (ClientPayload.encode message.clientPayload)

def decodeBody (bytes : List UInt8) : Option (ClientMessage × List UInt8) := do
  let (templateId, bytes) ← decodeUIntLE 2 bytes
  let (clientPayload, bytes) ← ClientPayload.decode templateId bytes
  pure ({ clientPayload }, bytes)

theorem decodeBody_encodeBody (message : ClientMessage) (rest : List UInt8) :
    decodeBody (encodeBody message ++ rest) = some (message, rest) := by
  unfold decodeBody encodeBody
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [ClientPayload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : ClientMessage) : (encodeBody message).length + 4 < 256 ^ 4 := by
  unfold encodeBody
  cases message.clientPayload with
  | approveTesTradeRequest inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length, ApproveTesTradeRequest.encode_length]
    omega
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
  | deleteTesTradeRequest inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length, DeleteTesTradeRequest.encode_length]
    omega
  | enterTesTradeRequest inner =>
    have bound_inner := EnterTesTradeRequest.encode_length_le inner
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length]
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
  | issuerSecurityStateChangeRequest inner =>
    have bound_inner := IssuerSecurityStateChangeRequest.encode_length_le inner
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length]
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
  | modifyTesTradeRequest inner =>
    have bound_inner := ModifyTesTradeRequest.encode_length_le inner
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | newOrderSingleRequest inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length, NewOrderSingleRequest.encode_length]
    omega
  | newOrderSingleShortRequest inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length, NewOrderSingleShortRequest.encode_length]
    omega
  | pingRequest inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length, PingRequest.encode_length]
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
  | singleQuoteRequest inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length, SingleQuoteRequest.encode_length]
    omega
  | specialistRfqRejectRequest inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length, SpecialistRfqRejectRequest.encode_length]
    omega
  | specialistRfqReplyRequest inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length, SpecialistRfqReplyRequest.encode_length]
    omega
  | specialistSecurityStateChangeRequest inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length, SpecialistSecurityStateChangeRequest.encode_length]
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
  | xetraEnLightEnterQuoteRequest inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length, XetraEnLightEnterQuoteRequest.encode_length]
    omega
  | xetraEnLightHitQuoteRequest inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length, XetraEnLightHitQuoteRequest.encode_length]
    omega
  | xetraEnLightOpenNegotiationRequest inner =>
    have bound_inner := XetraEnLightOpenNegotiationRequest.encode_length_le inner
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | xetraEnLightQuotingStatusRequest inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length, XetraEnLightQuotingStatusRequest.encode_length]
    omega
  | xetraEnLightUpdateNegotiationRequest inner =>
    have bound_inner := XetraEnLightUpdateNegotiationRequest.encode_length_le inner
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length]
    omega

/-- Size rule: Body Len counts the bytes after it plus 4, so it is written from the body and checked on decode -/
def encode : ClientMessage → List UInt8 :=
  encodeFramedLE 4 4 encodeBody

def decode : List UInt8 → Option (ClientMessage × List UInt8) :=
  decodeFramedLE 4 4 decodeBody

@[simp] theorem decode_encode (message : ClientMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramedLE_encodeFramedLE 4 4 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

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
  rw [decodeAll_encodeMany ClientMessage.encode ClientMessage.decode ClientMessage.decode_encode ClientMessage.encode_length_pos message.clientMessage _ (encodeMany_length_ge ClientMessage.encode ClientMessage.encode_length_pos message.clientMessage), some_bind]
  rfl

end ClientPacket

end Omi.EurexT7XtiFbeV100Client
