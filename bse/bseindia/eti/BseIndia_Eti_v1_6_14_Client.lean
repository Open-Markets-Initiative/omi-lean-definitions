import Omi.Wire

/-!
# BSE Limited Enhanced Trading Interface v1.6.14

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Debt Inquiry Request is not framed: its length Body Len is not an integer it reads.

Note: Delete All Order Request is not framed: its length Body Len is not an integer it reads.

Note: Delete All Quote Request is not framed: its length Body Len is not an integer it reads.

Note: Delete Order Complex Request is not framed: its length Body Len is not an integer it reads.

Note: Delete Order Single Request is not framed: its length Body Len is not an integer it reads.

Note: Gateway Request is not framed: its length Body Len is not an integer it reads.

Note: Heartbeat is not framed: its length Body Len is not an integer it reads.

Note: Inquire Session List Request is not framed: its length Body Len is not an integer it reads.

Note: Logon Request is not framed: its length Body Len is not an integer it reads.

Note: Logout Request is not framed: its length Body Len is not an integer it reads.

Note: Mass Quote Request is not framed: its length Body Len is not an integer it reads.

Note: Modify Order Complex Request is not framed: its length Body Len is not an integer it reads.

Note: Modify Order Single Request is not framed: its length Body Len is not an integer it reads.

Note: Modify Order Single Short Request is not framed: its length Body Len is not an integer it reads.

Note: Multi Leg Order Request is not framed: its length Body Len is not an integer it reads.

Note: New Order Complex Request is not framed: its length Body Len is not an integer it reads.

Note: New Order Single Request is not framed: its length Body Len is not an integer it reads.

Note: New Order Single Short Request is not framed: its length Body Len is not an integer it reads.

Note: Retransmit Me Message Request is not framed: its length Body Len is not an integer it reads.

Note: Retransmit Request is not framed: its length Body Len is not an integer it reads.

Note: Session Password Change Request is not framed: its length Body Len is not an integer it reads.

Note: Session Registration Request is not framed: its length Body Len is not an integer it reads.

Note: Subscribe Request is not framed: its length Body Len is not an integer it reads.

Note: Unsubscribe Request is not framed: its length Body Len is not an integer it reads.

Note: User Login Request is not framed: its length Body Len is not an integer it reads.

Note: User Logout Request is not framed: its length Body Len is not an integer it reads.

Note: User Password Change Request is not framed: its length Body Len is not an integer it reads.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.BseBseindiaEtiFbeV1614Client

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

/-- All Or None Flag: one byte code -/
def AllOrNoneFlag.codes : List UInt8 :=
  [0x59, 0x4E]

inductive AllOrNoneFlag where
  | useAllOrNone -- Use All Or None
  | useAllOrNoneNot -- Use All Or None Not
  | unlisted (byte : { byte : UInt8 // byte ∉ AllOrNoneFlag.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace AllOrNoneFlag

def toByte : AllOrNoneFlag → UInt8
  | .useAllOrNone => 0x59
  | .useAllOrNoneNot => 0x4E
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : AllOrNoneFlag :=
  if byte = 0x59 then .useAllOrNone
  else .useAllOrNoneNot

def ofByte (byte : UInt8) : AllOrNoneFlag :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : AllOrNoneFlag) : ofByte value.toByte = value := by
  cases value with
  | useAllOrNone => decide
  | useAllOrNoneNot => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : AllOrNoneFlag) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (AllOrNoneFlag × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : AllOrNoneFlag) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : AllOrNoneFlag) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end AllOrNoneFlag

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

/-- Debt Inquiry Request: 50 bytes -/
structure DebtInquiryRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  underlyingPx : BitVec 64
  yield : BitVec 64
  securityId : BitVec 64
  orderQty : BitVec 32
  pad4 : Alpha 4
  deriving DecidableEq, Repr

namespace DebtInquiryRequest

def encode (message : DebtInquiryRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 8 message.underlyingPx
    ++ (encodeUIntLE 8 message.yield
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 4 message.orderQty
    ++ (Alpha.encode message.pad4)))))))

def decode (bytes : List UInt8) : Option (DebtInquiryRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (underlyingPx, bytes) ← decodeUIntLE 8 bytes
  let (yield, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (orderQty, bytes) ← decodeUIntLE 4 bytes
  let (pad4, bytes) ← Alpha.decode 4 bytes
  pure ({ networkMsgId, pad2, requestHeaderComp, underlyingPx, yield, securityId, orderQty, pad4 }, bytes)

@[simp] theorem encode_length (message : DebtInquiryRequest) : (encode message).length = 50 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : DebtInquiryRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DebtInquiryRequest) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end DebtInquiryRequest

/-- Delete All Order Request: 58 bytes -/
structure DeleteAllOrderRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  securityId : BitVec 64
  marketSegmentId : BitVec 32
  regulatoryId : BitVec 32
  algoId : Alpha 16
  targetPartyIdSessionId : BitVec 32
  targetPartyIdExecutingTrader : BitVec 32
  deriving DecidableEq, Repr

namespace DeleteAllOrderRequest

def encode (message : DeleteAllOrderRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.regulatoryId
    ++ (Alpha.encode message.algoId
    ++ (encodeUIntLE 4 message.targetPartyIdSessionId
    ++ (encodeUIntLE 4 message.targetPartyIdExecutingTrader))))))))

def decode (bytes : List UInt8) : Option (DeleteAllOrderRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (regulatoryId, bytes) ← decodeUIntLE 4 bytes
  let (algoId, bytes) ← Alpha.decode 16 bytes
  let (targetPartyIdSessionId, bytes) ← decodeUIntLE 4 bytes
  let (targetPartyIdExecutingTrader, bytes) ← decodeUIntLE 4 bytes
  pure ({ networkMsgId, pad2, requestHeaderComp, securityId, marketSegmentId, regulatoryId, algoId, targetPartyIdSessionId, targetPartyIdExecutingTrader }, bytes)

@[simp] theorem encode_length (message : DeleteAllOrderRequest) : (encode message).length = 58 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length]

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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end DeleteAllOrderRequest

/-- Delete All Quote Request: 50 bytes -/
structure DeleteAllQuoteRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  marketSegmentId : BitVec 32
  targetPartyIdSessionId : BitVec 32
  algoId : Alpha 16
  regulatoryId : BitVec 32
  pad4 : Alpha 4
  deriving DecidableEq, Repr

namespace DeleteAllQuoteRequest

def encode (message : DeleteAllQuoteRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.targetPartyIdSessionId
    ++ (Alpha.encode message.algoId
    ++ (encodeUIntLE 4 message.regulatoryId
    ++ (Alpha.encode message.pad4)))))))

def decode (bytes : List UInt8) : Option (DeleteAllQuoteRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (targetPartyIdSessionId, bytes) ← decodeUIntLE 4 bytes
  let (algoId, bytes) ← Alpha.decode 16 bytes
  let (regulatoryId, bytes) ← decodeUIntLE 4 bytes
  let (pad4, bytes) ← Alpha.decode 4 bytes
  pure ({ networkMsgId, pad2, requestHeaderComp, marketSegmentId, targetPartyIdSessionId, algoId, regulatoryId, pad4 }, bytes)

@[simp] theorem encode_length (message : DeleteAllQuoteRequest) : (encode message).length = 50 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length]

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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end DeleteAllQuoteRequest

/-- Delete Order Complex Request: 90 bytes -/
structure DeleteOrderComplexRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  orderId : BitVec 64
  clOrdId : BitVec 64
  origClOrdId : BitVec 64
  securityId : BitVec 64
  filler1 : Alpha 8
  messageTag : BitVec 32
  marketSegmentId : BitVec 32
  targetPartyIdSessionId : BitVec 32
  regulatoryId : BitVec 32
  algoId : Alpha 16
  deriving DecidableEq, Repr

namespace DeleteOrderComplexRequest

def encode (message : DeleteOrderComplexRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 8 message.origClOrdId
    ++ (encodeUIntLE 8 message.securityId
    ++ (Alpha.encode message.filler1
    ++ (encodeUIntLE 4 message.messageTag
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.targetPartyIdSessionId
    ++ (encodeUIntLE 4 message.regulatoryId
    ++ (Alpha.encode message.algoId))))))))))))

def decode (bytes : List UInt8) : Option (DeleteOrderComplexRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (origClOrdId, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (filler1, bytes) ← Alpha.decode 8 bytes
  let (messageTag, bytes) ← decodeUIntLE 4 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (targetPartyIdSessionId, bytes) ← decodeUIntLE 4 bytes
  let (regulatoryId, bytes) ← decodeUIntLE 4 bytes
  let (algoId, bytes) ← Alpha.decode 16 bytes
  pure ({ networkMsgId, pad2, requestHeaderComp, orderId, clOrdId, origClOrdId, securityId, filler1, messageTag, marketSegmentId, targetPartyIdSessionId, regulatoryId, algoId }, bytes)

@[simp] theorem encode_length (message : DeleteOrderComplexRequest) : (encode message).length = 90 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : DeleteOrderComplexRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DeleteOrderComplexRequest) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end DeleteOrderComplexRequest

/-- Delete Order Single Request: 90 bytes -/
structure DeleteOrderSingleRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  orderId : BitVec 64
  clOrdId : BitVec 64
  origClOrdId : BitVec 64
  filler1 : Alpha 8
  messageTag : BitVec 32
  marketSegmentId : BitVec 32
  simpleSecurityId : BitVec 32
  targetPartyIdSessionId : BitVec 32
  regulatoryId : BitVec 32
  algoId : Alpha 16
  pad4 : Alpha 4
  deriving DecidableEq, Repr

namespace DeleteOrderSingleRequest

def encode (message : DeleteOrderSingleRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 8 message.origClOrdId
    ++ (Alpha.encode message.filler1
    ++ (encodeUIntLE 4 message.messageTag
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.simpleSecurityId
    ++ (encodeUIntLE 4 message.targetPartyIdSessionId
    ++ (encodeUIntLE 4 message.regulatoryId
    ++ (Alpha.encode message.algoId
    ++ (Alpha.encode message.pad4)))))))))))))

def decode (bytes : List UInt8) : Option (DeleteOrderSingleRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (origClOrdId, bytes) ← decodeUIntLE 8 bytes
  let (filler1, bytes) ← Alpha.decode 8 bytes
  let (messageTag, bytes) ← decodeUIntLE 4 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (simpleSecurityId, bytes) ← decodeUIntLE 4 bytes
  let (targetPartyIdSessionId, bytes) ← decodeUIntLE 4 bytes
  let (regulatoryId, bytes) ← decodeUIntLE 4 bytes
  let (algoId, bytes) ← Alpha.decode 16 bytes
  let (pad4, bytes) ← Alpha.decode 4 bytes
  pure ({ networkMsgId, pad2, requestHeaderComp, orderId, clOrdId, origClOrdId, filler1, messageTag, marketSegmentId, simpleSecurityId, targetPartyIdSessionId, regulatoryId, algoId, pad4 }, bytes)

@[simp] theorem encode_length (message : DeleteOrderSingleRequest) : (encode message).length = 90 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length]

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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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

end DeleteOrderSingleRequest

/-- Gateway Request: 90 bytes -/
structure GatewayRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  partyIdSessionId : BitVec 32
  defaultCstmApplVerId : Alpha 30
  password : Alpha 32
  pad6 : Alpha 6
  deriving DecidableEq, Repr

namespace GatewayRequest

def encode (message : GatewayRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 4 message.partyIdSessionId
    ++ (Alpha.encode message.defaultCstmApplVerId
    ++ (Alpha.encode message.password
    ++ (Alpha.encode message.pad6))))))

def decode (bytes : List UInt8) : Option (GatewayRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (partyIdSessionId, bytes) ← decodeUIntLE 4 bytes
  let (defaultCstmApplVerId, bytes) ← Alpha.decode 30 bytes
  let (password, bytes) ← Alpha.decode 32 bytes
  let (pad6, bytes) ← Alpha.decode 6 bytes
  pure ({ networkMsgId, pad2, requestHeaderComp, partyIdSessionId, defaultCstmApplVerId, password, pad6 }, bytes)

@[simp] theorem encode_length (message : GatewayRequest) : (encode message).length = 90 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : GatewayRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : GatewayRequest) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
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
  offerPx : BitVec 64
  bidSize : BitVec 32
  offerSize : BitVec 32
  messageTag : BitVec 32
  pad4 : Alpha 4
  deriving DecidableEq, Repr

namespace QuoteEntryGrpComp

def encode (message : QuoteEntryGrpComp) : List UInt8 :=
  encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.bidPx
    ++ (encodeUIntLE 8 message.offerPx
    ++ (encodeUIntLE 4 message.bidSize
    ++ (encodeUIntLE 4 message.offerSize
    ++ (encodeUIntLE 4 message.messageTag
    ++ (Alpha.encode message.pad4))))))

def decode (bytes : List UInt8) : Option (QuoteEntryGrpComp × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (bidPx, bytes) ← decodeUIntLE 8 bytes
  let (offerPx, bytes) ← decodeUIntLE 8 bytes
  let (bidSize, bytes) ← decodeUIntLE 4 bytes
  let (offerSize, bytes) ← decodeUIntLE 4 bytes
  let (messageTag, bytes) ← decodeUIntLE 4 bytes
  let (pad4, bytes) ← Alpha.decode 4 bytes
  pure ({ securityId, bidPx, offerPx, bidSize, offerSize, messageTag, pad4 }, bytes)

@[simp] theorem encode_length (message : QuoteEntryGrpComp) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end QuoteEntryGrpComp

/-- Mass Quote Request -/
structure MassQuoteRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  senderLocationId : BitVec 64
  quoteId : BitVec 64
  marketSegmentId : BitVec 32
  regulatoryId : BitVec 32
  enrichmentRuleId : BitVec 16
  accountType : BitVec 8
  priceValidityCheckType : BitVec 8
  quoteSizeType : BitVec 8
  stpcFlag : BitVec 8
  algoId : Alpha 16
  clientCode : Alpha 12
  cpCode : Alpha 12
  pad1 : Alpha 1
  quoteEntryGrpComp : Bounded 1 QuoteEntryGrpComp
  deriving DecidableEq, Repr

namespace MassQuoteRequest

def encode (message : MassQuoteRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 8 message.senderLocationId
    ++ (encodeUIntLE 8 message.quoteId
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.regulatoryId
    ++ (encodeUIntLE 2 message.enrichmentRuleId
    ++ (encodeUInt 1 message.accountType
    ++ (encodeUInt 1 message.priceValidityCheckType
    ++ (encodeUInt 1 message.quoteSizeType
    ++ (encodeUInt 1 message.stpcFlag
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.quoteEntryGrpComp.val.length)
    ++ (Alpha.encode message.algoId
    ++ (Alpha.encode message.clientCode
    ++ (Alpha.encode message.cpCode
    ++ (Alpha.encode message.pad1
    ++ (encodeMany QuoteEntryGrpComp.encode message.quoteEntryGrpComp.val)))))))))))))))))

def decode (bytes : List UInt8) : Option (MassQuoteRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (senderLocationId, bytes) ← decodeUIntLE 8 bytes
  let (quoteId, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (regulatoryId, bytes) ← decodeUIntLE 4 bytes
  let (enrichmentRuleId, bytes) ← decodeUIntLE 2 bytes
  let (accountType, bytes) ← decodeUInt 1 bytes
  let (priceValidityCheckType, bytes) ← decodeUInt 1 bytes
  let (quoteSizeType, bytes) ← decodeUInt 1 bytes
  let (stpcFlag, bytes) ← decodeUInt 1 bytes
  let (noQuoteEntries, bytes) ← decodeUInt 1 bytes
  let (algoId, bytes) ← Alpha.decode 16 bytes
  let (clientCode, bytes) ← Alpha.decode 12 bytes
  let (cpCode, bytes) ← Alpha.decode 12 bytes
  let (pad1, bytes) ← Alpha.decode 1 bytes
  let (quoteEntryGrpComp_, bytes) ← decodeMany QuoteEntryGrpComp.decode noQuoteEntries.toNat bytes
  if fits_quoteEntryGrpComp : quoteEntryGrpComp_.length < 256 ^ 1 then
    pure ({ networkMsgId, pad2, requestHeaderComp, senderLocationId, quoteId, marketSegmentId, regulatoryId, enrichmentRuleId, accountType, priceValidityCheckType, quoteSizeType, stpcFlag, algoId, clientCode, cpCode, pad1, quoteEntryGrpComp := ⟨quoteEntryGrpComp_, fits_quoteEntryGrpComp⟩ }, bytes)
  else none

theorem encode_length_pos (message : MassQuoteRequest) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MassQuoteRequest) : (encode message).length ≤ 10290 := by
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
  rw [decodeMany_bounded 1 QuoteEntryGrpComp.encode QuoteEntryGrpComp.decode QuoteEntryGrpComp.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.quoteEntryGrpComp.length_lt]
  rfl

end MassQuoteRequest

/-- Leg Ord Grp Comp: 8 bytes -/
structure LegOrdGrpComp where
  legAccount : Alpha 2
  legPositionEffect : Alpha 1
  pad5 : Alpha 5
  deriving DecidableEq, Repr

namespace LegOrdGrpComp

def encode (message : LegOrdGrpComp) : List UInt8 :=
  Alpha.encode message.legAccount
    ++ (Alpha.encode message.legPositionEffect
    ++ (Alpha.encode message.pad5))

def decode (bytes : List UInt8) : Option (LegOrdGrpComp × List UInt8) := do
  let (legAccount, bytes) ← Alpha.decode 2 bytes
  let (legPositionEffect, bytes) ← Alpha.decode 1 bytes
  let (pad5, bytes) ← Alpha.decode 5 bytes
  pure ({ legAccount, legPositionEffect, pad5 }, bytes)

@[simp] theorem encode_length (message : LegOrdGrpComp) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : LegOrdGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LegOrdGrpComp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end LegOrdGrpComp

/-- Modify Order Complex Request -/
structure ModifyOrderComplexRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  orderId : BitVec 64
  clOrdId : BitVec 64
  origClOrdId : BitVec 64
  securityId : BitVec 64
  price : BitVec 64
  maxPricePercentage : BitVec 64
  senderLocationId : BitVec 64
  activityTime : BitVec 64
  filler1 : Alpha 8
  filler2 : Alpha 4
  marketSegmentId : BitVec 32
  messageTag : BitVec 32
  orderQty : BitVec 32
  maxShow : BitVec 32
  expireDate : BitVec 32
  targetPartyIdSessionId : BitVec 32
  regulatoryId : BitVec 32
  filler4 : Alpha 2
  partyIdTakeUpTradingFirm : Alpha 5
  partyIdOrderOriginationFirm : Alpha 7
  partyIdBeneficiary : Alpha 9
  accountType : BitVec 8
  applSeqIndicator : BitVec 8
  productComplex : BitVec 8
  side : BitVec 8
  ordType : BitVec 8
  priceValidityCheckType : BitVec 8
  execInst : BitVec 8
  timeInForce : BitVec 8
  rolloverFlag : BitVec 8
  tradingCapacity : BitVec 8
  deltaQtyFlag : Alpha 1
  partyIdLocationId : Alpha 2
  custOrderHandlingInst : Alpha 1
  regulatoryText : Alpha 20
  algoId : Alpha 16
  clientCode : Alpha 12
  cpCode : Alpha 12
  freeText3 : Alpha 12
  pad2v2 : Alpha 2
  legOrdGrpComp : Bounded 1 LegOrdGrpComp
  deriving DecidableEq, Repr

namespace ModifyOrderComplexRequest

def encode (message : ModifyOrderComplexRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 8 message.origClOrdId
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 8 message.maxPricePercentage
    ++ (encodeUIntLE 8 message.senderLocationId
    ++ (encodeUIntLE 8 message.activityTime
    ++ (Alpha.encode message.filler1
    ++ (Alpha.encode message.filler2
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.messageTag
    ++ (encodeUIntLE 4 message.orderQty
    ++ (encodeUIntLE 4 message.maxShow
    ++ (encodeUIntLE 4 message.expireDate
    ++ (encodeUIntLE 4 message.targetPartyIdSessionId
    ++ (encodeUIntLE 4 message.regulatoryId
    ++ (Alpha.encode message.filler4
    ++ (Alpha.encode message.partyIdTakeUpTradingFirm
    ++ (Alpha.encode message.partyIdOrderOriginationFirm
    ++ (Alpha.encode message.partyIdBeneficiary
    ++ (encodeUInt 1 message.accountType
    ++ (encodeUInt 1 message.applSeqIndicator
    ++ (encodeUInt 1 message.productComplex
    ++ (encodeUInt 1 message.side
    ++ (encodeUInt 1 message.ordType
    ++ (encodeUInt 1 message.priceValidityCheckType
    ++ (encodeUInt 1 message.execInst
    ++ (encodeUInt 1 message.timeInForce
    ++ (encodeUInt 1 message.rolloverFlag
    ++ (encodeUInt 1 message.tradingCapacity
    ++ (Alpha.encode message.deltaQtyFlag
    ++ (Alpha.encode message.partyIdLocationId
    ++ (Alpha.encode message.custOrderHandlingInst
    ++ (Alpha.encode message.regulatoryText
    ++ (Alpha.encode message.algoId
    ++ (Alpha.encode message.clientCode
    ++ (Alpha.encode message.cpCode
    ++ (Alpha.encode message.freeText3
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.legOrdGrpComp.val.length)
    ++ (Alpha.encode message.pad2v2
    ++ (encodeMany LegOrdGrpComp.encode message.legOrdGrpComp.val))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (ModifyOrderComplexRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (origClOrdId, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (maxPricePercentage, bytes) ← decodeUIntLE 8 bytes
  let (senderLocationId, bytes) ← decodeUIntLE 8 bytes
  let (activityTime, bytes) ← decodeUIntLE 8 bytes
  let (filler1, bytes) ← Alpha.decode 8 bytes
  let (filler2, bytes) ← Alpha.decode 4 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (messageTag, bytes) ← decodeUIntLE 4 bytes
  let (orderQty, bytes) ← decodeUIntLE 4 bytes
  let (maxShow, bytes) ← decodeUIntLE 4 bytes
  let (expireDate, bytes) ← decodeUIntLE 4 bytes
  let (targetPartyIdSessionId, bytes) ← decodeUIntLE 4 bytes
  let (regulatoryId, bytes) ← decodeUIntLE 4 bytes
  let (filler4, bytes) ← Alpha.decode 2 bytes
  let (partyIdTakeUpTradingFirm, bytes) ← Alpha.decode 5 bytes
  let (partyIdOrderOriginationFirm, bytes) ← Alpha.decode 7 bytes
  let (partyIdBeneficiary, bytes) ← Alpha.decode 9 bytes
  let (accountType, bytes) ← decodeUInt 1 bytes
  let (applSeqIndicator, bytes) ← decodeUInt 1 bytes
  let (productComplex, bytes) ← decodeUInt 1 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (ordType, bytes) ← decodeUInt 1 bytes
  let (priceValidityCheckType, bytes) ← decodeUInt 1 bytes
  let (execInst, bytes) ← decodeUInt 1 bytes
  let (timeInForce, bytes) ← decodeUInt 1 bytes
  let (rolloverFlag, bytes) ← decodeUInt 1 bytes
  let (tradingCapacity, bytes) ← decodeUInt 1 bytes
  let (deltaQtyFlag, bytes) ← Alpha.decode 1 bytes
  let (partyIdLocationId, bytes) ← Alpha.decode 2 bytes
  let (custOrderHandlingInst, bytes) ← Alpha.decode 1 bytes
  let (regulatoryText, bytes) ← Alpha.decode 20 bytes
  let (algoId, bytes) ← Alpha.decode 16 bytes
  let (clientCode, bytes) ← Alpha.decode 12 bytes
  let (cpCode, bytes) ← Alpha.decode 12 bytes
  let (freeText3, bytes) ← Alpha.decode 12 bytes
  let (noLegs, bytes) ← decodeUInt 1 bytes
  let (pad2v2, bytes) ← Alpha.decode 2 bytes
  let (legOrdGrpComp_, bytes) ← decodeMany LegOrdGrpComp.decode noLegs.toNat bytes
  if fits_legOrdGrpComp : legOrdGrpComp_.length < 256 ^ 1 then
    pure ({ networkMsgId, pad2, requestHeaderComp, orderId, clOrdId, origClOrdId, securityId, price, maxPricePercentage, senderLocationId, activityTime, filler1, filler2, marketSegmentId, messageTag, orderQty, maxShow, expireDate, targetPartyIdSessionId, regulatoryId, filler4, partyIdTakeUpTradingFirm, partyIdOrderOriginationFirm, partyIdBeneficiary, accountType, applSeqIndicator, productComplex, side, ordType, priceValidityCheckType, execInst, timeInForce, rolloverFlag, tradingCapacity, deltaQtyFlag, partyIdLocationId, custOrderHandlingInst, regulatoryText, algoId, clientCode, cpCode, freeText3, pad2v2, legOrdGrpComp := ⟨legOrdGrpComp_, fits_legOrdGrpComp⟩ }, bytes)
  else none

theorem encode_length_pos (message : ModifyOrderComplexRequest) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ModifyOrderComplexRequest) : (encode message).length ≤ 2274 := by
  have bound_legOrdGrpComp := message.legOrdGrpComp.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const LegOrdGrpComp.encode 8 LegOrdGrpComp.encode_length]
  omega

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : ModifyOrderComplexRequest) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 LegOrdGrpComp.encode LegOrdGrpComp.decode LegOrdGrpComp.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.legOrdGrpComp.length_lt]
  rfl

end ModifyOrderComplexRequest

/-- Modify Order Single Request: 242 bytes -/
structure ModifyOrderSingleRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  orderId : BitVec 64
  clOrdId : BitVec 64
  origClOrdId : BitVec 64
  price : BitVec 64
  stopPx : BitVec 64
  maxPricePercentage : BitVec 64
  senderLocationId : BitVec 64
  activityTime : BitVec 64
  filler1 : Alpha 8
  filler2 : Alpha 4
  messageTag : BitVec 32
  orderQty : BitVec 32
  maxShow : BitVec 32
  expireDate : BitVec 32
  marketSegmentId : BitVec 32
  simpleSecurityId : BitVec 32
  targetPartyIdSessionId : BitVec 32
  regulatoryId : BitVec 32
  filler4 : Alpha 2
  partyIdTakeUpTradingFirm : Alpha 5
  partyIdOrderOriginationFirm : Alpha 7
  partyIdBeneficiary : Alpha 9
  accountType : BitVec 8
  applSeqIndicator : BitVec 8
  side : BitVec 8
  ordType : BitVec 8
  priceValidityCheckType : BitVec 8
  timeInForce : BitVec 8
  execInst : BitVec 8
  rolloverFlag : BitVec 8
  tradingSessionSubId : BitVec 8
  tradingCapacity : BitVec 8
  deltaQtyFlag : Alpha 1
  account : Alpha 2
  positionEffect : Alpha 1
  partyIdLocationId : Alpha 2
  custOrderHandlingInst : Alpha 1
  regulatoryText : Alpha 20
  algoId : Alpha 16
  clientCode : Alpha 12
  cpCode : Alpha 12
  freeText3 : Alpha 12
  pad4 : Alpha 4
  deriving DecidableEq, Repr

namespace ModifyOrderSingleRequest

def encode (message : ModifyOrderSingleRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 8 message.origClOrdId
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 8 message.stopPx
    ++ (encodeUIntLE 8 message.maxPricePercentage
    ++ (encodeUIntLE 8 message.senderLocationId
    ++ (encodeUIntLE 8 message.activityTime
    ++ (Alpha.encode message.filler1
    ++ (Alpha.encode message.filler2
    ++ (encodeUIntLE 4 message.messageTag
    ++ (encodeUIntLE 4 message.orderQty
    ++ (encodeUIntLE 4 message.maxShow
    ++ (encodeUIntLE 4 message.expireDate
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.simpleSecurityId
    ++ (encodeUIntLE 4 message.targetPartyIdSessionId
    ++ (encodeUIntLE 4 message.regulatoryId
    ++ (Alpha.encode message.filler4
    ++ (Alpha.encode message.partyIdTakeUpTradingFirm
    ++ (Alpha.encode message.partyIdOrderOriginationFirm
    ++ (Alpha.encode message.partyIdBeneficiary
    ++ (encodeUInt 1 message.accountType
    ++ (encodeUInt 1 message.applSeqIndicator
    ++ (encodeUInt 1 message.side
    ++ (encodeUInt 1 message.ordType
    ++ (encodeUInt 1 message.priceValidityCheckType
    ++ (encodeUInt 1 message.timeInForce
    ++ (encodeUInt 1 message.execInst
    ++ (encodeUInt 1 message.rolloverFlag
    ++ (encodeUInt 1 message.tradingSessionSubId
    ++ (encodeUInt 1 message.tradingCapacity
    ++ (Alpha.encode message.deltaQtyFlag
    ++ (Alpha.encode message.account
    ++ (Alpha.encode message.positionEffect
    ++ (Alpha.encode message.partyIdLocationId
    ++ (Alpha.encode message.custOrderHandlingInst
    ++ (Alpha.encode message.regulatoryText
    ++ (Alpha.encode message.algoId
    ++ (Alpha.encode message.clientCode
    ++ (Alpha.encode message.cpCode
    ++ (Alpha.encode message.freeText3
    ++ (Alpha.encode message.pad4)))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (ModifyOrderSingleRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (origClOrdId, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (stopPx, bytes) ← decodeUIntLE 8 bytes
  let (maxPricePercentage, bytes) ← decodeUIntLE 8 bytes
  let (senderLocationId, bytes) ← decodeUIntLE 8 bytes
  let (activityTime, bytes) ← decodeUIntLE 8 bytes
  let (filler1, bytes) ← Alpha.decode 8 bytes
  let (filler2, bytes) ← Alpha.decode 4 bytes
  let (messageTag, bytes) ← decodeUIntLE 4 bytes
  let (orderQty, bytes) ← decodeUIntLE 4 bytes
  let (maxShow, bytes) ← decodeUIntLE 4 bytes
  let (expireDate, bytes) ← decodeUIntLE 4 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (simpleSecurityId, bytes) ← decodeUIntLE 4 bytes
  let (targetPartyIdSessionId, bytes) ← decodeUIntLE 4 bytes
  let (regulatoryId, bytes) ← decodeUIntLE 4 bytes
  let (filler4, bytes) ← Alpha.decode 2 bytes
  let (partyIdTakeUpTradingFirm, bytes) ← Alpha.decode 5 bytes
  let (partyIdOrderOriginationFirm, bytes) ← Alpha.decode 7 bytes
  let (partyIdBeneficiary, bytes) ← Alpha.decode 9 bytes
  let (accountType, bytes) ← decodeUInt 1 bytes
  let (applSeqIndicator, bytes) ← decodeUInt 1 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (ordType, bytes) ← decodeUInt 1 bytes
  let (priceValidityCheckType, bytes) ← decodeUInt 1 bytes
  let (timeInForce, bytes) ← decodeUInt 1 bytes
  let (execInst, bytes) ← decodeUInt 1 bytes
  let (rolloverFlag, bytes) ← decodeUInt 1 bytes
  let (tradingSessionSubId, bytes) ← decodeUInt 1 bytes
  let (tradingCapacity, bytes) ← decodeUInt 1 bytes
  let (deltaQtyFlag, bytes) ← Alpha.decode 1 bytes
  let (account, bytes) ← Alpha.decode 2 bytes
  let (positionEffect, bytes) ← Alpha.decode 1 bytes
  let (partyIdLocationId, bytes) ← Alpha.decode 2 bytes
  let (custOrderHandlingInst, bytes) ← Alpha.decode 1 bytes
  let (regulatoryText, bytes) ← Alpha.decode 20 bytes
  let (algoId, bytes) ← Alpha.decode 16 bytes
  let (clientCode, bytes) ← Alpha.decode 12 bytes
  let (cpCode, bytes) ← Alpha.decode 12 bytes
  let (freeText3, bytes) ← Alpha.decode 12 bytes
  let (pad4, bytes) ← Alpha.decode 4 bytes
  pure ({ networkMsgId, pad2, requestHeaderComp, orderId, clOrdId, origClOrdId, price, stopPx, maxPricePercentage, senderLocationId, activityTime, filler1, filler2, messageTag, orderQty, maxShow, expireDate, marketSegmentId, simpleSecurityId, targetPartyIdSessionId, regulatoryId, filler4, partyIdTakeUpTradingFirm, partyIdOrderOriginationFirm, partyIdBeneficiary, accountType, applSeqIndicator, side, ordType, priceValidityCheckType, timeInForce, execInst, rolloverFlag, tradingSessionSubId, tradingCapacity, deltaQtyFlag, account, positionEffect, partyIdLocationId, custOrderHandlingInst, regulatoryText, algoId, clientCode, cpCode, freeText3, pad4 }, bytes)

@[simp] theorem encode_length (message : ModifyOrderSingleRequest) : (encode message).length = 242 := by
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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

/-- Modify Order Single Short Request: 130 bytes -/
structure ModifyOrderSingleShortRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  orderId : BitVec 64
  clOrdId : BitVec 64
  origClOrdId : BitVec 64
  price : BitVec 64
  senderLocationId : BitVec 64
  activityTime : BitVec 64
  orderQty : BitVec 32
  maxShow : BitVec 32
  simpleSecurityId : BitVec 32
  filler2 : Alpha 4
  filler4 : Alpha 2
  accountType : BitVec 8
  side : BitVec 8
  priceValidityCheckType : BitVec 8
  timeInForce : BitVec 8
  execInst : BitVec 8
  algoId : Alpha 16
  clientCode : Alpha 12
  cpCode : Alpha 12
  pad1 : Alpha 1
  deriving DecidableEq, Repr

namespace ModifyOrderSingleShortRequest

def encode (message : ModifyOrderSingleShortRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 8 message.origClOrdId
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 8 message.senderLocationId
    ++ (encodeUIntLE 8 message.activityTime
    ++ (encodeUIntLE 4 message.orderQty
    ++ (encodeUIntLE 4 message.maxShow
    ++ (encodeUIntLE 4 message.simpleSecurityId
    ++ (Alpha.encode message.filler2
    ++ (Alpha.encode message.filler4
    ++ (encodeUInt 1 message.accountType
    ++ (encodeUInt 1 message.side
    ++ (encodeUInt 1 message.priceValidityCheckType
    ++ (encodeUInt 1 message.timeInForce
    ++ (encodeUInt 1 message.execInst
    ++ (Alpha.encode message.algoId
    ++ (Alpha.encode message.clientCode
    ++ (Alpha.encode message.cpCode
    ++ (Alpha.encode message.pad1))))))))))))))))))))))

def decode (bytes : List UInt8) : Option (ModifyOrderSingleShortRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (origClOrdId, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (senderLocationId, bytes) ← decodeUIntLE 8 bytes
  let (activityTime, bytes) ← decodeUIntLE 8 bytes
  let (orderQty, bytes) ← decodeUIntLE 4 bytes
  let (maxShow, bytes) ← decodeUIntLE 4 bytes
  let (simpleSecurityId, bytes) ← decodeUIntLE 4 bytes
  let (filler2, bytes) ← Alpha.decode 4 bytes
  let (filler4, bytes) ← Alpha.decode 2 bytes
  let (accountType, bytes) ← decodeUInt 1 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (priceValidityCheckType, bytes) ← decodeUInt 1 bytes
  let (timeInForce, bytes) ← decodeUInt 1 bytes
  let (execInst, bytes) ← decodeUInt 1 bytes
  let (algoId, bytes) ← Alpha.decode 16 bytes
  let (clientCode, bytes) ← Alpha.decode 12 bytes
  let (cpCode, bytes) ← Alpha.decode 12 bytes
  let (pad1, bytes) ← Alpha.decode 1 bytes
  pure ({ networkMsgId, pad2, requestHeaderComp, orderId, clOrdId, origClOrdId, price, senderLocationId, activityTime, orderQty, maxShow, simpleSecurityId, filler2, filler4, accountType, side, priceValidityCheckType, timeInForce, execInst, algoId, clientCode, cpCode, pad1 }, bytes)

@[simp] theorem encode_length (message : ModifyOrderSingleShortRequest) : (encode message).length = 130 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : ModifyOrderSingleShortRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ModifyOrderSingleShortRequest

/-- Multi Leg Ord Grp Comp: 40 bytes -/
structure MultiLegOrdGrpComp where
  securityId : BitVec 64
  price : BitVec 64
  maxPricePercentage : BitVec 64
  messageTag : BitVec 32
  marketSegmentId : BitVec 32
  orderQty : BitVec 32
  productComplex : BitVec 8
  side : BitVec 8
  ordType : BitVec 8
  pad1 : Alpha 1
  deriving DecidableEq, Repr

namespace MultiLegOrdGrpComp

def encode (message : MultiLegOrdGrpComp) : List UInt8 :=
  encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 8 message.maxPricePercentage
    ++ (encodeUIntLE 4 message.messageTag
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.orderQty
    ++ (encodeUInt 1 message.productComplex
    ++ (encodeUInt 1 message.side
    ++ (encodeUInt 1 message.ordType
    ++ (Alpha.encode message.pad1)))))))))

def decode (bytes : List UInt8) : Option (MultiLegOrdGrpComp × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (maxPricePercentage, bytes) ← decodeUIntLE 8 bytes
  let (messageTag, bytes) ← decodeUIntLE 4 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (orderQty, bytes) ← decodeUIntLE 4 bytes
  let (productComplex, bytes) ← decodeUInt 1 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (ordType, bytes) ← decodeUInt 1 bytes
  let (pad1, bytes) ← Alpha.decode 1 bytes
  pure ({ securityId, price, maxPricePercentage, messageTag, marketSegmentId, orderQty, productComplex, side, ordType, pad1 }, bytes)

@[simp] theorem encode_length (message : MultiLegOrdGrpComp) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : MultiLegOrdGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MultiLegOrdGrpComp) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end MultiLegOrdGrpComp

/-- Multi Leg Order Request -/
structure MultiLegOrderRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  senderLocationId : BitVec 64
  clOrdId : BitVec 64
  accountType : BitVec 8
  allOrNoneFlag : AllOrNoneFlag
  algoId : Alpha 16
  clientCode : Alpha 12
  cpCode : Alpha 12
  pad5 : Alpha 5
  multiLegOrdGrpComp : Bounded 1 MultiLegOrdGrpComp
  deriving DecidableEq, Repr

namespace MultiLegOrderRequest

def encode (message : MultiLegOrderRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 8 message.senderLocationId
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUInt 1 message.accountType
    ++ (AllOrNoneFlag.encode message.allOrNoneFlag
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.multiLegOrdGrpComp.val.length)
    ++ (Alpha.encode message.algoId
    ++ (Alpha.encode message.clientCode
    ++ (Alpha.encode message.cpCode
    ++ (Alpha.encode message.pad5
    ++ (encodeMany MultiLegOrdGrpComp.encode message.multiLegOrdGrpComp.val))))))))))))

def decode (bytes : List UInt8) : Option (MultiLegOrderRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (senderLocationId, bytes) ← decodeUIntLE 8 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (accountType, bytes) ← decodeUInt 1 bytes
  let (allOrNoneFlag, bytes) ← AllOrNoneFlag.decode bytes
  let (noOfMultiLeg, bytes) ← decodeUInt 1 bytes
  let (algoId, bytes) ← Alpha.decode 16 bytes
  let (clientCode, bytes) ← Alpha.decode 12 bytes
  let (cpCode, bytes) ← Alpha.decode 12 bytes
  let (pad5, bytes) ← Alpha.decode 5 bytes
  let (multiLegOrdGrpComp_, bytes) ← decodeMany MultiLegOrdGrpComp.decode noOfMultiLeg.toNat bytes
  if fits_multiLegOrdGrpComp : multiLegOrdGrpComp_.length < 256 ^ 1 then
    pure ({ networkMsgId, pad2, requestHeaderComp, senderLocationId, clOrdId, accountType, allOrNoneFlag, algoId, clientCode, cpCode, pad5, multiLegOrdGrpComp := ⟨multiLegOrdGrpComp_, fits_multiLegOrdGrpComp⟩ }, bytes)
  else none

theorem encode_length_pos (message : MultiLegOrderRequest) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MultiLegOrderRequest) : (encode message).length ≤ 10282 := by
  have bound_multiLegOrdGrpComp := message.multiLegOrdGrpComp.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length, AllOrNoneFlag.encode_length, encodeMany_length_const MultiLegOrdGrpComp.encode 40 MultiLegOrdGrpComp.encode_length]
  omega

@[simp] theorem decode_encode (message : MultiLegOrderRequest) (rest : List UInt8) :
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
  rw [List.append_assoc, AllOrNoneFlag.decode_encode, some_bind]
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
  rw [decodeMany_bounded 1 MultiLegOrdGrpComp.encode MultiLegOrdGrpComp.decode MultiLegOrdGrpComp.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.multiLegOrdGrpComp.length_lt]
  rfl

end MultiLegOrderRequest

/-- New Order Complex Request -/
structure NewOrderComplexRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  clOrdId : BitVec 64
  securityId : BitVec 64
  maxPricePercentage : BitVec 64
  senderLocationId : BitVec 64
  price : BitVec 64
  filler1 : Alpha 8
  filler2 : Alpha 4
  messageTag : BitVec 32
  marketSegmentId : BitVec 32
  orderQty : BitVec 32
  maxShow : BitVec 32
  expireDate : BitVec 32
  regulatoryId : BitVec 32
  filler4 : Alpha 2
  partyIdTakeUpTradingFirm : Alpha 5
  partyIdOrderOriginationFirm : Alpha 7
  partyIdBeneficiary : Alpha 9
  accountType : BitVec 8
  applSeqIndicator : BitVec 8
  productComplex : BitVec 8
  side : BitVec 8
  ordType : BitVec 8
  priceValidityCheckType : BitVec 8
  execInst : BitVec 8
  timeInForce : BitVec 8
  stpcFlag : BitVec 8
  rolloverFlag : BitVec 8
  tradingCapacity : BitVec 8
  partyIdLocationId : Alpha 2
  regulatoryText : Alpha 20
  algoId : Alpha 16
  custOrderHandlingInst : Alpha 1
  clientCode : Alpha 12
  cpCode : Alpha 12
  freeText3 : Alpha 12
  pad6 : Alpha 6
  legOrdGrpComp : Bounded 1 LegOrdGrpComp
  deriving DecidableEq, Repr

namespace NewOrderComplexRequest

def encode (message : NewOrderComplexRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.maxPricePercentage
    ++ (encodeUIntLE 8 message.senderLocationId
    ++ (encodeUIntLE 8 message.price
    ++ (Alpha.encode message.filler1
    ++ (Alpha.encode message.filler2
    ++ (encodeUIntLE 4 message.messageTag
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.orderQty
    ++ (encodeUIntLE 4 message.maxShow
    ++ (encodeUIntLE 4 message.expireDate
    ++ (encodeUIntLE 4 message.regulatoryId
    ++ (Alpha.encode message.filler4
    ++ (Alpha.encode message.partyIdTakeUpTradingFirm
    ++ (Alpha.encode message.partyIdOrderOriginationFirm
    ++ (Alpha.encode message.partyIdBeneficiary
    ++ (encodeUInt 1 message.accountType
    ++ (encodeUInt 1 message.applSeqIndicator
    ++ (encodeUInt 1 message.productComplex
    ++ (encodeUInt 1 message.side
    ++ (encodeUInt 1 message.ordType
    ++ (encodeUInt 1 message.priceValidityCheckType
    ++ (encodeUInt 1 message.execInst
    ++ (encodeUInt 1 message.timeInForce
    ++ (encodeUInt 1 message.stpcFlag
    ++ (encodeUInt 1 message.rolloverFlag
    ++ (encodeUInt 1 message.tradingCapacity
    ++ (Alpha.encode message.partyIdLocationId
    ++ (Alpha.encode message.regulatoryText
    ++ (Alpha.encode message.algoId
    ++ (Alpha.encode message.custOrderHandlingInst
    ++ (Alpha.encode message.clientCode
    ++ (Alpha.encode message.cpCode
    ++ (Alpha.encode message.freeText3
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.legOrdGrpComp.val.length)
    ++ (Alpha.encode message.pad6
    ++ (encodeMany LegOrdGrpComp.encode message.legOrdGrpComp.val))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (NewOrderComplexRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (maxPricePercentage, bytes) ← decodeUIntLE 8 bytes
  let (senderLocationId, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (filler1, bytes) ← Alpha.decode 8 bytes
  let (filler2, bytes) ← Alpha.decode 4 bytes
  let (messageTag, bytes) ← decodeUIntLE 4 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (orderQty, bytes) ← decodeUIntLE 4 bytes
  let (maxShow, bytes) ← decodeUIntLE 4 bytes
  let (expireDate, bytes) ← decodeUIntLE 4 bytes
  let (regulatoryId, bytes) ← decodeUIntLE 4 bytes
  let (filler4, bytes) ← Alpha.decode 2 bytes
  let (partyIdTakeUpTradingFirm, bytes) ← Alpha.decode 5 bytes
  let (partyIdOrderOriginationFirm, bytes) ← Alpha.decode 7 bytes
  let (partyIdBeneficiary, bytes) ← Alpha.decode 9 bytes
  let (accountType, bytes) ← decodeUInt 1 bytes
  let (applSeqIndicator, bytes) ← decodeUInt 1 bytes
  let (productComplex, bytes) ← decodeUInt 1 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (ordType, bytes) ← decodeUInt 1 bytes
  let (priceValidityCheckType, bytes) ← decodeUInt 1 bytes
  let (execInst, bytes) ← decodeUInt 1 bytes
  let (timeInForce, bytes) ← decodeUInt 1 bytes
  let (stpcFlag, bytes) ← decodeUInt 1 bytes
  let (rolloverFlag, bytes) ← decodeUInt 1 bytes
  let (tradingCapacity, bytes) ← decodeUInt 1 bytes
  let (partyIdLocationId, bytes) ← Alpha.decode 2 bytes
  let (regulatoryText, bytes) ← Alpha.decode 20 bytes
  let (algoId, bytes) ← Alpha.decode 16 bytes
  let (custOrderHandlingInst, bytes) ← Alpha.decode 1 bytes
  let (clientCode, bytes) ← Alpha.decode 12 bytes
  let (cpCode, bytes) ← Alpha.decode 12 bytes
  let (freeText3, bytes) ← Alpha.decode 12 bytes
  let (noLegs, bytes) ← decodeUInt 1 bytes
  let (pad6, bytes) ← Alpha.decode 6 bytes
  let (legOrdGrpComp_, bytes) ← decodeMany LegOrdGrpComp.decode noLegs.toNat bytes
  if fits_legOrdGrpComp : legOrdGrpComp_.length < 256 ^ 1 then
    pure ({ networkMsgId, pad2, requestHeaderComp, clOrdId, securityId, maxPricePercentage, senderLocationId, price, filler1, filler2, messageTag, marketSegmentId, orderQty, maxShow, expireDate, regulatoryId, filler4, partyIdTakeUpTradingFirm, partyIdOrderOriginationFirm, partyIdBeneficiary, accountType, applSeqIndicator, productComplex, side, ordType, priceValidityCheckType, execInst, timeInForce, stpcFlag, rolloverFlag, tradingCapacity, partyIdLocationId, regulatoryText, algoId, custOrderHandlingInst, clientCode, cpCode, freeText3, pad6, legOrdGrpComp := ⟨legOrdGrpComp_, fits_legOrdGrpComp⟩ }, bytes)
  else none

theorem encode_length_pos (message : NewOrderComplexRequest) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : NewOrderComplexRequest) : (encode message).length ≤ 2250 := by
  have bound_legOrdGrpComp := message.legOrdGrpComp.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const LegOrdGrpComp.encode 8 LegOrdGrpComp.encode_length]
  omega

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : NewOrderComplexRequest) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 LegOrdGrpComp.encode LegOrdGrpComp.decode LegOrdGrpComp.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.legOrdGrpComp.length_lt]
  rfl

end NewOrderComplexRequest

/-- New Order Single Request: 210 bytes -/
structure NewOrderSingleRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  price : BitVec 64
  stopPx : BitVec 64
  maxPricePercentage : BitVec 64
  senderLocationId : BitVec 64
  clOrdId : BitVec 64
  filler1 : Alpha 8
  filler2 : Alpha 4
  messageTag : BitVec 32
  orderQty : BitVec 32
  maxShow : BitVec 32
  expireDate : BitVec 32
  marketSegmentId : BitVec 32
  simpleSecurityId : BitVec 32
  regulatoryId : BitVec 32
  filler4 : Alpha 2
  partyIdTakeUpTradingFirm : Alpha 5
  partyIdOrderOriginationFirm : Alpha 7
  partyIdBeneficiary : Alpha 9
  accountType : BitVec 8
  applSeqIndicator : BitVec 8
  side : BitVec 8
  ordType : BitVec 8
  priceValidityCheckType : BitVec 8
  timeInForce : BitVec 8
  execInst : BitVec 8
  stpcFlag : BitVec 8
  rolloverFlag : BitVec 8
  tradingSessionSubId : BitVec 8
  tradingCapacity : BitVec 8
  account : Alpha 2
  positionEffect : Alpha 1
  partyIdLocationId : Alpha 2
  custOrderHandlingInst : Alpha 1
  regulatoryText : Alpha 20
  algoId : Alpha 16
  clientCode : Alpha 12
  cpCode : Alpha 12
  freeText3 : Alpha 12
  deriving DecidableEq, Repr

namespace NewOrderSingleRequest

def encode (message : NewOrderSingleRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 8 message.stopPx
    ++ (encodeUIntLE 8 message.maxPricePercentage
    ++ (encodeUIntLE 8 message.senderLocationId
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (Alpha.encode message.filler1
    ++ (Alpha.encode message.filler2
    ++ (encodeUIntLE 4 message.messageTag
    ++ (encodeUIntLE 4 message.orderQty
    ++ (encodeUIntLE 4 message.maxShow
    ++ (encodeUIntLE 4 message.expireDate
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.simpleSecurityId
    ++ (encodeUIntLE 4 message.regulatoryId
    ++ (Alpha.encode message.filler4
    ++ (Alpha.encode message.partyIdTakeUpTradingFirm
    ++ (Alpha.encode message.partyIdOrderOriginationFirm
    ++ (Alpha.encode message.partyIdBeneficiary
    ++ (encodeUInt 1 message.accountType
    ++ (encodeUInt 1 message.applSeqIndicator
    ++ (encodeUInt 1 message.side
    ++ (encodeUInt 1 message.ordType
    ++ (encodeUInt 1 message.priceValidityCheckType
    ++ (encodeUInt 1 message.timeInForce
    ++ (encodeUInt 1 message.execInst
    ++ (encodeUInt 1 message.stpcFlag
    ++ (encodeUInt 1 message.rolloverFlag
    ++ (encodeUInt 1 message.tradingSessionSubId
    ++ (encodeUInt 1 message.tradingCapacity
    ++ (Alpha.encode message.account
    ++ (Alpha.encode message.positionEffect
    ++ (Alpha.encode message.partyIdLocationId
    ++ (Alpha.encode message.custOrderHandlingInst
    ++ (Alpha.encode message.regulatoryText
    ++ (Alpha.encode message.algoId
    ++ (Alpha.encode message.clientCode
    ++ (Alpha.encode message.cpCode
    ++ (Alpha.encode message.freeText3))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (NewOrderSingleRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (stopPx, bytes) ← decodeUIntLE 8 bytes
  let (maxPricePercentage, bytes) ← decodeUIntLE 8 bytes
  let (senderLocationId, bytes) ← decodeUIntLE 8 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (filler1, bytes) ← Alpha.decode 8 bytes
  let (filler2, bytes) ← Alpha.decode 4 bytes
  let (messageTag, bytes) ← decodeUIntLE 4 bytes
  let (orderQty, bytes) ← decodeUIntLE 4 bytes
  let (maxShow, bytes) ← decodeUIntLE 4 bytes
  let (expireDate, bytes) ← decodeUIntLE 4 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (simpleSecurityId, bytes) ← decodeUIntLE 4 bytes
  let (regulatoryId, bytes) ← decodeUIntLE 4 bytes
  let (filler4, bytes) ← Alpha.decode 2 bytes
  let (partyIdTakeUpTradingFirm, bytes) ← Alpha.decode 5 bytes
  let (partyIdOrderOriginationFirm, bytes) ← Alpha.decode 7 bytes
  let (partyIdBeneficiary, bytes) ← Alpha.decode 9 bytes
  let (accountType, bytes) ← decodeUInt 1 bytes
  let (applSeqIndicator, bytes) ← decodeUInt 1 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (ordType, bytes) ← decodeUInt 1 bytes
  let (priceValidityCheckType, bytes) ← decodeUInt 1 bytes
  let (timeInForce, bytes) ← decodeUInt 1 bytes
  let (execInst, bytes) ← decodeUInt 1 bytes
  let (stpcFlag, bytes) ← decodeUInt 1 bytes
  let (rolloverFlag, bytes) ← decodeUInt 1 bytes
  let (tradingSessionSubId, bytes) ← decodeUInt 1 bytes
  let (tradingCapacity, bytes) ← decodeUInt 1 bytes
  let (account, bytes) ← Alpha.decode 2 bytes
  let (positionEffect, bytes) ← Alpha.decode 1 bytes
  let (partyIdLocationId, bytes) ← Alpha.decode 2 bytes
  let (custOrderHandlingInst, bytes) ← Alpha.decode 1 bytes
  let (regulatoryText, bytes) ← Alpha.decode 20 bytes
  let (algoId, bytes) ← Alpha.decode 16 bytes
  let (clientCode, bytes) ← Alpha.decode 12 bytes
  let (cpCode, bytes) ← Alpha.decode 12 bytes
  let (freeText3, bytes) ← Alpha.decode 12 bytes
  pure ({ networkMsgId, pad2, requestHeaderComp, price, stopPx, maxPricePercentage, senderLocationId, clOrdId, filler1, filler2, messageTag, orderQty, maxShow, expireDate, marketSegmentId, simpleSecurityId, regulatoryId, filler4, partyIdTakeUpTradingFirm, partyIdOrderOriginationFirm, partyIdBeneficiary, accountType, applSeqIndicator, side, ordType, priceValidityCheckType, timeInForce, execInst, stpcFlag, rolloverFlag, tradingSessionSubId, tradingCapacity, account, positionEffect, partyIdLocationId, custOrderHandlingInst, regulatoryText, algoId, clientCode, cpCode, freeText3 }, bytes)

@[simp] theorem encode_length (message : NewOrderSingleRequest) : (encode message).length = 210 := by
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end NewOrderSingleRequest

/-- New Order Single Short Request: 106 bytes -/
structure NewOrderSingleShortRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  price : BitVec 64
  senderLocationId : BitVec 64
  clOrdId : BitVec 64
  orderQty : BitVec 32
  maxShow : BitVec 32
  simpleSecurityId : BitVec 32
  filler2 : Alpha 4
  filler4 : Alpha 2
  accountType : BitVec 8
  side : BitVec 8
  priceValidityCheckType : BitVec 8
  timeInForce : BitVec 8
  stpcFlag : BitVec 8
  execInst : BitVec 8
  algoId : Alpha 16
  clientCode : Alpha 12
  cpCode : Alpha 12
  deriving DecidableEq, Repr

namespace NewOrderSingleShortRequest

def encode (message : NewOrderSingleShortRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 8 message.senderLocationId
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 4 message.orderQty
    ++ (encodeUIntLE 4 message.maxShow
    ++ (encodeUIntLE 4 message.simpleSecurityId
    ++ (Alpha.encode message.filler2
    ++ (Alpha.encode message.filler4
    ++ (encodeUInt 1 message.accountType
    ++ (encodeUInt 1 message.side
    ++ (encodeUInt 1 message.priceValidityCheckType
    ++ (encodeUInt 1 message.timeInForce
    ++ (encodeUInt 1 message.stpcFlag
    ++ (encodeUInt 1 message.execInst
    ++ (Alpha.encode message.algoId
    ++ (Alpha.encode message.clientCode
    ++ (Alpha.encode message.cpCode)))))))))))))))))))

def decode (bytes : List UInt8) : Option (NewOrderSingleShortRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (senderLocationId, bytes) ← decodeUIntLE 8 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (orderQty, bytes) ← decodeUIntLE 4 bytes
  let (maxShow, bytes) ← decodeUIntLE 4 bytes
  let (simpleSecurityId, bytes) ← decodeUIntLE 4 bytes
  let (filler2, bytes) ← Alpha.decode 4 bytes
  let (filler4, bytes) ← Alpha.decode 2 bytes
  let (accountType, bytes) ← decodeUInt 1 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (priceValidityCheckType, bytes) ← decodeUInt 1 bytes
  let (timeInForce, bytes) ← decodeUInt 1 bytes
  let (stpcFlag, bytes) ← decodeUInt 1 bytes
  let (execInst, bytes) ← decodeUInt 1 bytes
  let (algoId, bytes) ← Alpha.decode 16 bytes
  let (clientCode, bytes) ← Alpha.decode 12 bytes
  let (cpCode, bytes) ← Alpha.decode 12 bytes
  pure ({ networkMsgId, pad2, requestHeaderComp, price, senderLocationId, clOrdId, orderQty, maxShow, simpleSecurityId, filler2, filler4, accountType, side, priceValidityCheckType, timeInForce, stpcFlag, execInst, algoId, clientCode, cpCode }, bytes)

@[simp] theorem encode_length (message : NewOrderSingleShortRequest) : (encode message).length = 106 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : NewOrderSingleShortRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end NewOrderSingleShortRequest

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
  subscriptionScope : BitVec 32
  partitionId : BitVec 16
  refApplId : BitVec 8
  pad1 : Alpha 1
  deriving DecidableEq, Repr

namespace RetransmitRequest

def encode (message : RetransmitRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 8 message.applBegSeqNum
    ++ (encodeUIntLE 8 message.applEndSeqNum
    ++ (encodeUIntLE 4 message.subscriptionScope
    ++ (encodeUIntLE 2 message.partitionId
    ++ (encodeUInt 1 message.refApplId
    ++ (Alpha.encode message.pad1))))))))

def decode (bytes : List UInt8) : Option (RetransmitRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (applBegSeqNum, bytes) ← decodeUIntLE 8 bytes
  let (applEndSeqNum, bytes) ← decodeUIntLE 8 bytes
  let (subscriptionScope, bytes) ← decodeUIntLE 4 bytes
  let (partitionId, bytes) ← decodeUIntLE 2 bytes
  let (refApplId, bytes) ← decodeUInt 1 bytes
  let (pad1, bytes) ← Alpha.decode 1 bytes
  pure ({ networkMsgId, pad2, requestHeaderComp, applBegSeqNum, applEndSeqNum, subscriptionScope, partitionId, refApplId, pad1 }, bytes)

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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end RetransmitRequest

/-- Session Password Change Request: 90 bytes -/
structure SessionPasswordChangeRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  partyIdSessionId : BitVec 32
  password : Alpha 32
  newPassword : Alpha 32
  pad4 : Alpha 4
  deriving DecidableEq, Repr

namespace SessionPasswordChangeRequest

def encode (message : SessionPasswordChangeRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 4 message.partyIdSessionId
    ++ (Alpha.encode message.password
    ++ (Alpha.encode message.newPassword
    ++ (Alpha.encode message.pad4))))))

def decode (bytes : List UInt8) : Option (SessionPasswordChangeRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (partyIdSessionId, bytes) ← decodeUIntLE 4 bytes
  let (password, bytes) ← Alpha.decode 32 bytes
  let (newPassword, bytes) ← Alpha.decode 32 bytes
  let (pad4, bytes) ← Alpha.decode 4 bytes
  pure ({ networkMsgId, pad2, requestHeaderComp, partyIdSessionId, password, newPassword, pad4 }, bytes)

@[simp] theorem encode_length (message : SessionPasswordChangeRequest) : (encode message).length = 90 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : SessionPasswordChangeRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SessionPasswordChangeRequest) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SessionPasswordChangeRequest

/-- Session Registration Request: 34 bytes -/
structure SessionRegistrationRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  partyIdSessionId : BitVec 32
  pad4 : Alpha 4
  filler1 : Alpha 8
  deriving DecidableEq, Repr

namespace SessionRegistrationRequest

def encode (message : SessionRegistrationRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 4 message.partyIdSessionId
    ++ (Alpha.encode message.pad4
    ++ (Alpha.encode message.filler1)))))

def decode (bytes : List UInt8) : Option (SessionRegistrationRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (partyIdSessionId, bytes) ← decodeUIntLE 4 bytes
  let (pad4, bytes) ← Alpha.decode 4 bytes
  let (filler1, bytes) ← Alpha.decode 8 bytes
  pure ({ networkMsgId, pad2, requestHeaderComp, partyIdSessionId, pad4, filler1 }, bytes)

@[simp] theorem encode_length (message : SessionRegistrationRequest) : (encode message).length = 34 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : SessionRegistrationRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SessionRegistrationRequest) (rest : List UInt8) :
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

end SessionRegistrationRequest

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

/-- User Password Change Request: 90 bytes -/
structure UserPasswordChangeRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  username : BitVec 32
  password : Alpha 32
  newPassword : Alpha 32
  pad4 : Alpha 4
  deriving DecidableEq, Repr

namespace UserPasswordChangeRequest

def encode (message : UserPasswordChangeRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 4 message.username
    ++ (Alpha.encode message.password
    ++ (Alpha.encode message.newPassword
    ++ (Alpha.encode message.pad4))))))

def decode (bytes : List UInt8) : Option (UserPasswordChangeRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (username, bytes) ← decodeUIntLE 4 bytes
  let (password, bytes) ← Alpha.decode 32 bytes
  let (newPassword, bytes) ← Alpha.decode 32 bytes
  let (pad4, bytes) ← Alpha.decode 4 bytes
  pure ({ networkMsgId, pad2, requestHeaderComp, username, password, newPassword, pad4 }, bytes)

@[simp] theorem encode_length (message : UserPasswordChangeRequest) : (encode message).length = 90 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : UserPasswordChangeRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UserPasswordChangeRequest) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end UserPasswordChangeRequest

/-- Any Client Payload, selected by Template Id -/
inductive ClientPayload where
  | debtInquiryRequest (message : DebtInquiryRequest) -- 10390
  | deleteAllOrderRequest (message : DeleteAllOrderRequest) -- 10120
  | deleteAllQuoteRequest (message : DeleteAllQuoteRequest) -- 10408
  | deleteOrderComplexRequest (message : DeleteOrderComplexRequest) -- 10123
  | deleteOrderSingleRequest (message : DeleteOrderSingleRequest) -- 10109
  | gatewayRequest (message : GatewayRequest) -- 10020
  | heartbeat (message : Heartbeat) -- 10011
  | inquireSessionListRequest (message : InquireSessionListRequest) -- 10035
  | logonRequest (message : LogonRequest) -- 10000
  | logoutRequest (message : LogoutRequest) -- 10002
  | massQuoteRequest (message : MassQuoteRequest) -- 10405
  | modifyOrderComplexRequest (message : ModifyOrderComplexRequest) -- 10114
  | modifyOrderSingleRequest (message : ModifyOrderSingleRequest) -- 10106
  | modifyOrderSingleShortRequest (message : ModifyOrderSingleShortRequest) -- 10126
  | multiLegOrderRequest (message : MultiLegOrderRequest) -- 10991
  | newOrderComplexRequest (message : NewOrderComplexRequest) -- 10113
  | newOrderSingleRequest (message : NewOrderSingleRequest) -- 10100
  | newOrderSingleShortRequest (message : NewOrderSingleShortRequest) -- 10125
  | retransmitMeMessageRequest (message : RetransmitMeMessageRequest) -- 10026
  | retransmitRequest (message : RetransmitRequest) -- 10008
  | sessionPasswordChangeRequest (message : SessionPasswordChangeRequest) -- 10997
  | sessionRegistrationRequest (message : SessionRegistrationRequest) -- 10053
  | subscribeRequest (message : SubscribeRequest) -- 10025
  | unsubscribeRequest (message : UnsubscribeRequest) -- 10006
  | userLoginRequest (message : UserLoginRequest) -- 10018
  | userLogoutRequest (message : UserLogoutRequest) -- 10029
  | userPasswordChangeRequest (message : UserPasswordChangeRequest) -- 10996
  deriving DecidableEq, Repr

namespace ClientPayload

/-- The Template Id each message is sent under -/
def tag : ClientPayload → BitVec 16
  | .debtInquiryRequest _ => 10390
  | .deleteAllOrderRequest _ => 10120
  | .deleteAllQuoteRequest _ => 10408
  | .deleteOrderComplexRequest _ => 10123
  | .deleteOrderSingleRequest _ => 10109
  | .gatewayRequest _ => 10020
  | .heartbeat _ => 10011
  | .inquireSessionListRequest _ => 10035
  | .logonRequest _ => 10000
  | .logoutRequest _ => 10002
  | .massQuoteRequest _ => 10405
  | .modifyOrderComplexRequest _ => 10114
  | .modifyOrderSingleRequest _ => 10106
  | .modifyOrderSingleShortRequest _ => 10126
  | .multiLegOrderRequest _ => 10991
  | .newOrderComplexRequest _ => 10113
  | .newOrderSingleRequest _ => 10100
  | .newOrderSingleShortRequest _ => 10125
  | .retransmitMeMessageRequest _ => 10026
  | .retransmitRequest _ => 10008
  | .sessionPasswordChangeRequest _ => 10997
  | .sessionRegistrationRequest _ => 10053
  | .subscribeRequest _ => 10025
  | .unsubscribeRequest _ => 10006
  | .userLoginRequest _ => 10018
  | .userLogoutRequest _ => 10029
  | .userPasswordChangeRequest _ => 10996

def encode : ClientPayload → List UInt8
  | .debtInquiryRequest message => DebtInquiryRequest.encode message
  | .deleteAllOrderRequest message => DeleteAllOrderRequest.encode message
  | .deleteAllQuoteRequest message => DeleteAllQuoteRequest.encode message
  | .deleteOrderComplexRequest message => DeleteOrderComplexRequest.encode message
  | .deleteOrderSingleRequest message => DeleteOrderSingleRequest.encode message
  | .gatewayRequest message => GatewayRequest.encode message
  | .heartbeat message => Heartbeat.encode message
  | .inquireSessionListRequest message => InquireSessionListRequest.encode message
  | .logonRequest message => LogonRequest.encode message
  | .logoutRequest message => LogoutRequest.encode message
  | .massQuoteRequest message => MassQuoteRequest.encode message
  | .modifyOrderComplexRequest message => ModifyOrderComplexRequest.encode message
  | .modifyOrderSingleRequest message => ModifyOrderSingleRequest.encode message
  | .modifyOrderSingleShortRequest message => ModifyOrderSingleShortRequest.encode message
  | .multiLegOrderRequest message => MultiLegOrderRequest.encode message
  | .newOrderComplexRequest message => NewOrderComplexRequest.encode message
  | .newOrderSingleRequest message => NewOrderSingleRequest.encode message
  | .newOrderSingleShortRequest message => NewOrderSingleShortRequest.encode message
  | .retransmitMeMessageRequest message => RetransmitMeMessageRequest.encode message
  | .retransmitRequest message => RetransmitRequest.encode message
  | .sessionPasswordChangeRequest message => SessionPasswordChangeRequest.encode message
  | .sessionRegistrationRequest message => SessionRegistrationRequest.encode message
  | .subscribeRequest message => SubscribeRequest.encode message
  | .unsubscribeRequest message => UnsubscribeRequest.encode message
  | .userLoginRequest message => UserLoginRequest.encode message
  | .userLogoutRequest message => UserLogoutRequest.encode message
  | .userPasswordChangeRequest message => UserPasswordChangeRequest.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : ClientPayload) : (encode message).length ≤ 10290 := by
  cases message with
  | debtInquiryRequest inner =>
    simp only [encode, DebtInquiryRequest.encode_length]
    omega
  | deleteAllOrderRequest inner =>
    simp only [encode, DeleteAllOrderRequest.encode_length]
    omega
  | deleteAllQuoteRequest inner =>
    simp only [encode, DeleteAllQuoteRequest.encode_length]
    omega
  | deleteOrderComplexRequest inner =>
    simp only [encode, DeleteOrderComplexRequest.encode_length]
    omega
  | deleteOrderSingleRequest inner =>
    simp only [encode, DeleteOrderSingleRequest.encode_length]
    omega
  | gatewayRequest inner =>
    simp only [encode, GatewayRequest.encode_length]
    omega
  | heartbeat inner =>
    simp only [encode, Heartbeat.encode_length]
    omega
  | inquireSessionListRequest inner =>
    simp only [encode, InquireSessionListRequest.encode_length]
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
  | modifyOrderComplexRequest inner =>
    have bound_inner := ModifyOrderComplexRequest.encode_length_le inner
    simp only [encode]
    omega
  | modifyOrderSingleRequest inner =>
    simp only [encode, ModifyOrderSingleRequest.encode_length]
    omega
  | modifyOrderSingleShortRequest inner =>
    simp only [encode, ModifyOrderSingleShortRequest.encode_length]
    omega
  | multiLegOrderRequest inner =>
    have bound_inner := MultiLegOrderRequest.encode_length_le inner
    simp only [encode]
    omega
  | newOrderComplexRequest inner =>
    have bound_inner := NewOrderComplexRequest.encode_length_le inner
    simp only [encode]
    omega
  | newOrderSingleRequest inner =>
    simp only [encode, NewOrderSingleRequest.encode_length]
    omega
  | newOrderSingleShortRequest inner =>
    simp only [encode, NewOrderSingleShortRequest.encode_length]
    omega
  | retransmitMeMessageRequest inner =>
    simp only [encode, RetransmitMeMessageRequest.encode_length]
    omega
  | retransmitRequest inner =>
    simp only [encode, RetransmitRequest.encode_length]
    omega
  | sessionPasswordChangeRequest inner =>
    simp only [encode, SessionPasswordChangeRequest.encode_length]
    omega
  | sessionRegistrationRequest inner =>
    simp only [encode, SessionRegistrationRequest.encode_length]
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
  | userPasswordChangeRequest inner =>
    simp only [encode, UserPasswordChangeRequest.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (ClientPayload × List UInt8) :=
  if tag = 10390 then (DebtInquiryRequest.decode bytes).map fun (message, rest) => (.debtInquiryRequest message, rest)
  else if tag = 10120 then (DeleteAllOrderRequest.decode bytes).map fun (message, rest) => (.deleteAllOrderRequest message, rest)
  else if tag = 10408 then (DeleteAllQuoteRequest.decode bytes).map fun (message, rest) => (.deleteAllQuoteRequest message, rest)
  else if tag = 10123 then (DeleteOrderComplexRequest.decode bytes).map fun (message, rest) => (.deleteOrderComplexRequest message, rest)
  else if tag = 10109 then (DeleteOrderSingleRequest.decode bytes).map fun (message, rest) => (.deleteOrderSingleRequest message, rest)
  else if tag = 10020 then (GatewayRequest.decode bytes).map fun (message, rest) => (.gatewayRequest message, rest)
  else if tag = 10011 then (Heartbeat.decode bytes).map fun (message, rest) => (.heartbeat message, rest)
  else if tag = 10035 then (InquireSessionListRequest.decode bytes).map fun (message, rest) => (.inquireSessionListRequest message, rest)
  else if tag = 10000 then (LogonRequest.decode bytes).map fun (message, rest) => (.logonRequest message, rest)
  else if tag = 10002 then (LogoutRequest.decode bytes).map fun (message, rest) => (.logoutRequest message, rest)
  else if tag = 10405 then (MassQuoteRequest.decode bytes).map fun (message, rest) => (.massQuoteRequest message, rest)
  else if tag = 10114 then (ModifyOrderComplexRequest.decode bytes).map fun (message, rest) => (.modifyOrderComplexRequest message, rest)
  else if tag = 10106 then (ModifyOrderSingleRequest.decode bytes).map fun (message, rest) => (.modifyOrderSingleRequest message, rest)
  else if tag = 10126 then (ModifyOrderSingleShortRequest.decode bytes).map fun (message, rest) => (.modifyOrderSingleShortRequest message, rest)
  else if tag = 10991 then (MultiLegOrderRequest.decode bytes).map fun (message, rest) => (.multiLegOrderRequest message, rest)
  else if tag = 10113 then (NewOrderComplexRequest.decode bytes).map fun (message, rest) => (.newOrderComplexRequest message, rest)
  else if tag = 10100 then (NewOrderSingleRequest.decode bytes).map fun (message, rest) => (.newOrderSingleRequest message, rest)
  else if tag = 10125 then (NewOrderSingleShortRequest.decode bytes).map fun (message, rest) => (.newOrderSingleShortRequest message, rest)
  else if tag = 10026 then (RetransmitMeMessageRequest.decode bytes).map fun (message, rest) => (.retransmitMeMessageRequest message, rest)
  else if tag = 10008 then (RetransmitRequest.decode bytes).map fun (message, rest) => (.retransmitRequest message, rest)
  else if tag = 10997 then (SessionPasswordChangeRequest.decode bytes).map fun (message, rest) => (.sessionPasswordChangeRequest message, rest)
  else if tag = 10053 then (SessionRegistrationRequest.decode bytes).map fun (message, rest) => (.sessionRegistrationRequest message, rest)
  else if tag = 10025 then (SubscribeRequest.decode bytes).map fun (message, rest) => (.subscribeRequest message, rest)
  else if tag = 10006 then (UnsubscribeRequest.decode bytes).map fun (message, rest) => (.unsubscribeRequest message, rest)
  else if tag = 10018 then (UserLoginRequest.decode bytes).map fun (message, rest) => (.userLoginRequest message, rest)
  else if tag = 10029 then (UserLogoutRequest.decode bytes).map fun (message, rest) => (.userLogoutRequest message, rest)
  else if tag = 10996 then (UserPasswordChangeRequest.decode bytes).map fun (message, rest) => (.userPasswordChangeRequest message, rest)
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
  | debtInquiryRequest inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length, DebtInquiryRequest.encode_length]
    omega
  | deleteAllOrderRequest inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length, DeleteAllOrderRequest.encode_length]
    omega
  | deleteAllQuoteRequest inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length, DeleteAllQuoteRequest.encode_length]
    omega
  | deleteOrderComplexRequest inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length, DeleteOrderComplexRequest.encode_length]
    omega
  | deleteOrderSingleRequest inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length, DeleteOrderSingleRequest.encode_length]
    omega
  | gatewayRequest inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length, GatewayRequest.encode_length]
    omega
  | heartbeat inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length, Heartbeat.encode_length]
    omega
  | inquireSessionListRequest inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length, InquireSessionListRequest.encode_length]
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
  | modifyOrderComplexRequest inner =>
    have bound_inner := ModifyOrderComplexRequest.encode_length_le inner
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | modifyOrderSingleRequest inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length, ModifyOrderSingleRequest.encode_length]
    omega
  | modifyOrderSingleShortRequest inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length, ModifyOrderSingleShortRequest.encode_length]
    omega
  | multiLegOrderRequest inner =>
    have bound_inner := MultiLegOrderRequest.encode_length_le inner
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | newOrderComplexRequest inner =>
    have bound_inner := NewOrderComplexRequest.encode_length_le inner
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | newOrderSingleRequest inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length, NewOrderSingleRequest.encode_length]
    omega
  | newOrderSingleShortRequest inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length, NewOrderSingleShortRequest.encode_length]
    omega
  | retransmitMeMessageRequest inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length, RetransmitMeMessageRequest.encode_length]
    omega
  | retransmitRequest inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length, RetransmitRequest.encode_length]
    omega
  | sessionPasswordChangeRequest inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length, SessionPasswordChangeRequest.encode_length]
    omega
  | sessionRegistrationRequest inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length, SessionRegistrationRequest.encode_length]
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
  | userPasswordChangeRequest inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length, UserPasswordChangeRequest.encode_length]
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

end Omi.BseBseindiaEtiFbeV1614Client
