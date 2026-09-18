import Omi.Wire

/-!
# Eurex Exchange Enhanced Trading Interface v12.1

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Add Complex Instrument Request is not framed: its length Body Len is not an integer it reads.

Note: Add Flexible Instrument Request is not framed: its length Body Len is not an integer it reads.

Note: Add Scaled Simple Instrument Request is not framed: its length Body Len is not an integer it reads.

Note: Amend Basket Trade Request is not framed: its length Body Len is not an integer it reads.

Note: Approve Basket Trade Request is not framed: its length Body Len is not an integer it reads.

Note: Approve Reverse Tes Trade Request is not framed: its length Body Len is not an integer it reads.

Note: Approve Tes Trade Request is not framed: its length Body Len is not an integer it reads.

Note: Cross Request is not framed: its length Body Len is not an integer it reads.

Note: Delete All Order Request is not framed: its length Body Len is not an integer it reads.

Note: Delete All Quote Request is not framed: its length Body Len is not an integer it reads.

Note: Delete Basket Trade Request is not framed: its length Body Len is not an integer it reads.

Note: Delete Clip Request is not framed: its length Body Len is not an integer it reads.

Note: Delete Order Complex Request is not framed: its length Body Len is not an integer it reads.

Note: Delete Order Request is not framed: its length Body Len is not an integer it reads.

Note: Delete Order Single Request is not framed: its length Body Len is not an integer it reads.

Note: Delete Tes Trade Request is not framed: its length Body Len is not an integer it reads.

Note: Enter Basket Trade Request is not framed: its length Body Len is not an integer it reads.

Note: Enter Clip Request is not framed: its length Body Len is not an integer it reads.

Note: Enter Tes Trade Request is not framed: its length Body Len is not an integer it reads.

Note: Heartbeat is not framed: its length Body Len is not an integer it reads.

Note: Inquire Enrichment Rule Id List Request is not framed: its length Body Len is not an integer it reads.

Note: Inquire Mm Parameter Request is not framed: its length Body Len is not an integer it reads.

Note: Inquire Margin Based Risk Limit Request is not framed: its length Body Len is not an integer it reads.

Note: Inquire Pre Trade Risk Limits Request is not framed: its length Body Len is not an integer it reads.

Note: Inquire Session List Request is not framed: its length Body Len is not an integer it reads.

Note: Inquire User Request is not framed: its length Body Len is not an integer it reads.

Note: Logon Request is not framed: its length Body Len is not an integer it reads.

Note: Logon Request Encrypted is not framed: its length Body Len is not an integer it reads.

Note: Logout Request is not framed: its length Body Len is not an integer it reads.

Note: Mm Parameter Definition Request is not framed: its length Body Len is not an integer it reads.

Note: Mass Order is not framed: its length Body Len is not an integer it reads.

Note: Mass Quote Request is not framed: its length Body Len is not an integer it reads.

Note: Modify Basket Trade Request is not framed: its length Body Len is not an integer it reads.

Note: Modify Order Complex Request is not framed: its length Body Len is not an integer it reads.

Note: Modify Order Complex Short Request is not framed: its length Body Len is not an integer it reads.

Note: Modify Order Request is not framed: its length Body Len is not an integer it reads.

Note: Modify Order Short Request is not framed: its length Body Len is not an integer it reads.

Note: Modify Order Single Request is not framed: its length Body Len is not an integer it reads.

Note: Modify Order Single Short Request is not framed: its length Body Len is not an integer it reads.

Note: Modify Tes Trade Request is not framed: its length Body Len is not an integer it reads.

Note: New Order Complex Request is not framed: its length Body Len is not an integer it reads.

Note: New Order Complex Short Request is not framed: its length Body Len is not an integer it reads.

Note: New Order Request is not framed: its length Body Len is not an integer it reads.

Note: New Order Short Request is not framed: its length Body Len is not an integer it reads.

Note: New Order Single Request is not framed: its length Body Len is not an integer it reads.

Note: New Order Single Short Request is not framed: its length Body Len is not an integer it reads.

Note: Ping Request is not framed: its length Body Len is not an integer it reads.

Note: Pre Trade Risk Limits Definition Request is not framed: its length Body Len is not an integer it reads.

Note: Quote Activation Request is not framed: its length Body Len is not an integer it reads.

Note: Rfq Request is not framed: its length Body Len is not an integer it reads.

Note: Retransmit Me Message Request is not framed: its length Body Len is not an integer it reads.

Note: Retransmit Request is not framed: its length Body Len is not an integer it reads.

Note: Reverse Tes Trade Request is not framed: its length Body Len is not an integer it reads.

Note: Srqs Enter Quote Request is not framed: its length Body Len is not an integer it reads.

Note: Srqs Hit Quote Request is not framed: its length Body Len is not an integer it reads.

Note: Srqs Inquire Smart Respondent Request is not framed: its length Body Len is not an integer it reads.

Note: Srqs Open Negotiation Request is not framed: its length Body Len is not an integer it reads.

Note: Srqs Quote Snapshot Request is not framed: its length Body Len is not an integer it reads.

Note: Srqs Quoting Status Request is not framed: its length Body Len is not an integer it reads.

Note: Srqs Update Deal Status Request is not framed: its length Body Len is not an integer it reads.

Note: Srqs Update Negotiation Request is not framed: its length Body Len is not an integer it reads.

Note: Subscribe Request is not framed: its length Body Len is not an integer it reads.

Note: Unsubscribe Request is not framed: its length Body Len is not an integer it reads.

Note: Update Remaining Risk Allowance Base Request is not framed: its length Body Len is not an integer it reads.

Note: Upload Tes Trade Request is not framed: its length Body Len is not an integer it reads.

Note: User Login Request is not framed: its length Body Len is not an integer it reads.

Note: User Login Request Encrypted is not framed: its length Body Len is not an integer it reads.

Note: User Logout Request is not framed: its length Body Len is not an integer it reads.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.EurexT7EtiFbeV121Client

/-- Settl Method: one byte code -/
def SettlMethod.codes : List UInt8 :=
  [0x43, 0x50]

inductive SettlMethod where
  | cashSettlement -- Cash Settlement
  | physicalSettlement -- Physical Settlement
  | unlisted (byte : { byte : UInt8 // byte ∉ SettlMethod.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace SettlMethod

def toByte : SettlMethod → UInt8
  | .cashSettlement => 0x43
  | .physicalSettlement => 0x50
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : SettlMethod :=
  if byte = 0x43 then .cashSettlement
  else .physicalSettlement

def ofByte (byte : UInt8) : SettlMethod :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : SettlMethod) : ofByte value.toByte = value := by
  cases value with
  | cashSettlement => decide
  | physicalSettlement => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : SettlMethod) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (SettlMethod × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : SettlMethod) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : SettlMethod) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end SettlMethod

/-- Position Effect: one byte code -/
def PositionEffect.codes : List UInt8 :=
  [0x43, 0x4F]

inductive PositionEffect where
  | close -- Close
  | open_ -- Open
  | unlisted (byte : { byte : UInt8 // byte ∉ PositionEffect.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace PositionEffect

def toByte : PositionEffect → UInt8
  | .close => 0x43
  | .open_ => 0x4F
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : PositionEffect :=
  if byte = 0x43 then .close
  else .open_

def ofByte (byte : UInt8) : PositionEffect :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : PositionEffect) : ofByte value.toByte = value := by
  cases value with
  | close => decide
  | open_ => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : PositionEffect) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (PositionEffect × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : PositionEffect) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : PositionEffect) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end PositionEffect

/-- Cust Order Handling Inst: one byte code -/
def CustOrderHandlingInst.codes : List UInt8 :=
  [0x57, 0x59, 0x43, 0x47, 0x48, 0x44]

inductive CustOrderHandlingInst where
  | w -- W
  | y -- Y
  | c -- C
  | g -- G
  | h -- H
  | d -- D
  | unlisted (byte : { byte : UInt8 // byte ∉ CustOrderHandlingInst.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace CustOrderHandlingInst

def toByte : CustOrderHandlingInst → UInt8
  | .w => 0x57
  | .y => 0x59
  | .c => 0x43
  | .g => 0x47
  | .h => 0x48
  | .d => 0x44
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : CustOrderHandlingInst :=
  if byte = 0x57 then .w
  else if byte = 0x59 then .y
  else if byte = 0x43 then .c
  else if byte = 0x47 then .g
  else if byte = 0x48 then .h
  else .d

def ofByte (byte : UInt8) : CustOrderHandlingInst :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : CustOrderHandlingInst) : ofByte value.toByte = value := by
  cases value with
  | w => decide
  | y => decide
  | c => decide
  | g => decide
  | h => decide
  | d => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : CustOrderHandlingInst) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (CustOrderHandlingInst × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : CustOrderHandlingInst) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : CustOrderHandlingInst) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end CustOrderHandlingInst

/-- Leg Position Effect: one byte code -/
def LegPositionEffect.codes : List UInt8 :=
  [0x43, 0x4F]

inductive LegPositionEffect where
  | close -- Close
  | open_ -- Open
  | unlisted (byte : { byte : UInt8 // byte ∉ LegPositionEffect.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace LegPositionEffect

def toByte : LegPositionEffect → UInt8
  | .close => 0x43
  | .open_ => 0x4F
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : LegPositionEffect :=
  if byte = 0x43 then .close
  else .open_

def ofByte (byte : UInt8) : LegPositionEffect :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : LegPositionEffect) : ofByte value.toByte = value := by
  cases value with
  | close => decide
  | open_ => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : LegPositionEffect) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (LegPositionEffect × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : LegPositionEffect) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : LegPositionEffect) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end LegPositionEffect

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

/-- Quote Condition: one byte code -/
def QuoteCondition.codes : List UInt8 :=
  [0x41, 0x42, 0x7A, 0x38]

inductive QuoteCondition where
  | active -- Active
  | closed -- Closed
  | suspended -- Suspended
  | expired -- Expired
  | unlisted (byte : { byte : UInt8 // byte ∉ QuoteCondition.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace QuoteCondition

def toByte : QuoteCondition → UInt8
  | .active => 0x41
  | .closed => 0x42
  | .suspended => 0x7A
  | .expired => 0x38
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : QuoteCondition :=
  if byte = 0x41 then .active
  else if byte = 0x42 then .closed
  else if byte = 0x7A then .suspended
  else .expired

def ofByte (byte : UInt8) : QuoteCondition :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : QuoteCondition) : ofByte value.toByte = value := by
  cases value with
  | active => decide
  | closed => decide
  | suspended => decide
  | expired => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : QuoteCondition) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (QuoteCondition × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : QuoteCondition) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : QuoteCondition) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end QuoteCondition

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

/-- Instrmt Leg Grp Comp: 32 bytes -/
structure InstrmtLegGrpComp where
  legSecurityId : BitVec 64
  legPrice : BitVec 64
  legSymbol : BitVec 32
  legRatioQty : BitVec 32
  legSide : BitVec 8
  legSecurityType : BitVec 8
  pad6 : Alpha 6
  deriving DecidableEq, Repr

namespace InstrmtLegGrpComp

def encode (message : InstrmtLegGrpComp) : List UInt8 :=
  encodeUIntLE 8 message.legSecurityId
    ++ (encodeUIntLE 8 message.legPrice
    ++ (encodeUIntLE 4 message.legSymbol
    ++ (encodeUIntLE 4 message.legRatioQty
    ++ (encodeUInt 1 message.legSide
    ++ (encodeUInt 1 message.legSecurityType
    ++ (Alpha.encode message.pad6))))))

def decode (bytes : List UInt8) : Option (InstrmtLegGrpComp × List UInt8) := do
  let (legSecurityId, bytes) ← decodeUIntLE 8 bytes
  let (legPrice, bytes) ← decodeUIntLE 8 bytes
  let (legSymbol, bytes) ← decodeUIntLE 4 bytes
  let (legRatioQty, bytes) ← decodeUIntLE 4 bytes
  let (legSide, bytes) ← decodeUInt 1 bytes
  let (legSecurityType, bytes) ← decodeUInt 1 bytes
  let (pad6, bytes) ← Alpha.decode 6 bytes
  pure ({ legSecurityId, legPrice, legSymbol, legRatioQty, legSide, legSecurityType, pad6 }, bytes)

@[simp] theorem encode_length (message : InstrmtLegGrpComp) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : InstrmtLegGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstrmtLegGrpComp) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end InstrmtLegGrpComp

/-- Add Complex Instrument Request -/
structure AddComplexInstrumentRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  marketSegmentId : BitVec 32
  securitySubType : BitVec 32
  quantityScalingFactor : BitVec 16
  productComplex : BitVec 8
  multilegModel : BitVec 8
  complianceText : Alpha 20
  pad7 : Alpha 7
  instrmtLegGrpComp : Bounded 1 InstrmtLegGrpComp
  deriving DecidableEq, Repr

namespace AddComplexInstrumentRequest

def encode (message : AddComplexInstrumentRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.securitySubType
    ++ (encodeUIntLE 2 message.quantityScalingFactor
    ++ (encodeUInt 1 message.productComplex
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.instrmtLegGrpComp.val.length)
    ++ (encodeUInt 1 message.multilegModel
    ++ (Alpha.encode message.complianceText
    ++ (Alpha.encode message.pad7
    ++ (encodeMany InstrmtLegGrpComp.encode message.instrmtLegGrpComp.val)))))))))))

def decode (bytes : List UInt8) : Option (AddComplexInstrumentRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (securitySubType, bytes) ← decodeUIntLE 4 bytes
  let (quantityScalingFactor, bytes) ← decodeUIntLE 2 bytes
  let (productComplex, bytes) ← decodeUInt 1 bytes
  let (noLegOnbooks, bytes) ← decodeUInt 1 bytes
  let (multilegModel, bytes) ← decodeUInt 1 bytes
  let (complianceText, bytes) ← Alpha.decode 20 bytes
  let (pad7, bytes) ← Alpha.decode 7 bytes
  let (instrmtLegGrpComp_, bytes) ← decodeMany InstrmtLegGrpComp.decode noLegOnbooks.toNat bytes
  if fits_instrmtLegGrpComp : instrmtLegGrpComp_.length < 256 ^ 1 then
    pure ({ networkMsgId, pad2, requestHeaderComp, marketSegmentId, securitySubType, quantityScalingFactor, productComplex, multilegModel, complianceText, pad7, instrmtLegGrpComp := ⟨instrmtLegGrpComp_, fits_instrmtLegGrpComp⟩ }, bytes)
  else none

theorem encode_length_pos (message : AddComplexInstrumentRequest) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : AddComplexInstrumentRequest) : (encode message).length ≤ 8218 := by
  have bound_instrmtLegGrpComp := message.instrmtLegGrpComp.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const InstrmtLegGrpComp.encode 32 InstrmtLegGrpComp.encode_length]
  omega

@[simp] theorem decode_encode (message : AddComplexInstrumentRequest) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 InstrmtLegGrpComp.encode InstrmtLegGrpComp.decode InstrmtLegGrpComp.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.instrmtLegGrpComp.length_lt]
  rfl

end AddComplexInstrumentRequest

/-- Add Flexible Instrument Request: 66 bytes -/
structure AddFlexibleInstrumentRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  strikePrice : BitVec 64
  marketSegmentId : BitVec 32
  maturityDate : BitVec 32
  contractDate : BitVec 32
  settlMethod : SettlMethod
  optAttribute : BitVec 8
  putOrCall : BitVec 8
  exerciseStyle : BitVec 8
  complianceText : Alpha 20
  pad4 : Alpha 4
  deriving DecidableEq, Repr

namespace AddFlexibleInstrumentRequest

def encode (message : AddFlexibleInstrumentRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 8 message.strikePrice
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.maturityDate
    ++ (encodeUIntLE 4 message.contractDate
    ++ (SettlMethod.encode message.settlMethod
    ++ (encodeUInt 1 message.optAttribute
    ++ (encodeUInt 1 message.putOrCall
    ++ (encodeUInt 1 message.exerciseStyle
    ++ (Alpha.encode message.complianceText
    ++ (Alpha.encode message.pad4))))))))))))

def decode (bytes : List UInt8) : Option (AddFlexibleInstrumentRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (strikePrice, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (maturityDate, bytes) ← decodeUIntLE 4 bytes
  let (contractDate, bytes) ← decodeUIntLE 4 bytes
  let (settlMethod, bytes) ← SettlMethod.decode bytes
  let (optAttribute, bytes) ← decodeUInt 1 bytes
  let (putOrCall, bytes) ← decodeUInt 1 bytes
  let (exerciseStyle, bytes) ← decodeUInt 1 bytes
  let (complianceText, bytes) ← Alpha.decode 20 bytes
  let (pad4, bytes) ← Alpha.decode 4 bytes
  pure ({ networkMsgId, pad2, requestHeaderComp, strikePrice, marketSegmentId, maturityDate, contractDate, settlMethod, optAttribute, putOrCall, exerciseStyle, complianceText, pad4 }, bytes)

@[simp] theorem encode_length (message : AddFlexibleInstrumentRequest) : (encode message).length = 66 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length, SettlMethod.encode_length, encodeUInt_length]

theorem encode_length_pos (message : AddFlexibleInstrumentRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AddFlexibleInstrumentRequest) (rest : List UInt8) :
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
  rw [List.append_assoc, SettlMethod.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end AddFlexibleInstrumentRequest

/-- Add Scaled Simple Instrument Request: 34 bytes -/
structure AddScaledSimpleInstrumentRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  relatedSecurityId : BitVec 64
  marketSegmentId : BitVec 32
  quantityScalingFactor : BitVec 16
  multilegModel : BitVec 8
  pad1 : Alpha 1
  deriving DecidableEq, Repr

namespace AddScaledSimpleInstrumentRequest

def encode (message : AddScaledSimpleInstrumentRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 8 message.relatedSecurityId
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 2 message.quantityScalingFactor
    ++ (encodeUInt 1 message.multilegModel
    ++ (Alpha.encode message.pad1)))))))

def decode (bytes : List UInt8) : Option (AddScaledSimpleInstrumentRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (relatedSecurityId, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (quantityScalingFactor, bytes) ← decodeUIntLE 2 bytes
  let (multilegModel, bytes) ← decodeUInt 1 bytes
  let (pad1, bytes) ← Alpha.decode 1 bytes
  pure ({ networkMsgId, pad2, requestHeaderComp, relatedSecurityId, marketSegmentId, quantityScalingFactor, multilegModel, pad1 }, bytes)

@[simp] theorem encode_length (message : AddScaledSimpleInstrumentRequest) : (encode message).length = 34 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : AddScaledSimpleInstrumentRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AddScaledSimpleInstrumentRequest) (rest : List UInt8) :
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

end AddScaledSimpleInstrumentRequest

/-- Basket Root Party Grp Comp: 40 bytes -/
structure BasketRootPartyGrpComp where
  rootPartySubIdType : BitVec 16
  rootPartyContraFirm : Alpha 5
  rootPartyContraTrader : Alpha 6
  basketSideTradeReportId : Alpha 20
  pad7 : Alpha 7
  deriving DecidableEq, Repr

namespace BasketRootPartyGrpComp

def encode (message : BasketRootPartyGrpComp) : List UInt8 :=
  encodeUIntLE 2 message.rootPartySubIdType
    ++ (Alpha.encode message.rootPartyContraFirm
    ++ (Alpha.encode message.rootPartyContraTrader
    ++ (Alpha.encode message.basketSideTradeReportId
    ++ (Alpha.encode message.pad7))))

def decode (bytes : List UInt8) : Option (BasketRootPartyGrpComp × List UInt8) := do
  let (rootPartySubIdType, bytes) ← decodeUIntLE 2 bytes
  let (rootPartyContraFirm, bytes) ← Alpha.decode 5 bytes
  let (rootPartyContraTrader, bytes) ← Alpha.decode 6 bytes
  let (basketSideTradeReportId, bytes) ← Alpha.decode 20 bytes
  let (pad7, bytes) ← Alpha.decode 7 bytes
  pure ({ rootPartySubIdType, rootPartyContraFirm, rootPartyContraTrader, basketSideTradeReportId, pad7 }, bytes)

@[simp] theorem encode_length (message : BasketRootPartyGrpComp) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : BasketRootPartyGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BasketRootPartyGrpComp) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end BasketRootPartyGrpComp

/-- Instrmt Match Side Grp Comp: 80 bytes -/
structure InstrmtMatchSideGrpComp where
  securityId : BitVec 64
  lastPx : BitVec 64
  transBkdTime : BitVec 64
  relatedClosePrice : BitVec 64
  clearingTradePrice : BitVec 64
  packageId : BitVec 32
  sideMarketSegmentId : BitVec 32
  sideTrdSubTyp : BitVec 16
  productComplex : BitVec 8
  tradePublishIndicator : BitVec 8
  instrmtMatchSideId : BitVec 8
  effectOnBasket : BitVec 8
  tradeReportText : Alpha 20
  pad6 : Alpha 6
  deriving DecidableEq, Repr

namespace InstrmtMatchSideGrpComp

def encode (message : InstrmtMatchSideGrpComp) : List UInt8 :=
  encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.lastPx
    ++ (encodeUIntLE 8 message.transBkdTime
    ++ (encodeUIntLE 8 message.relatedClosePrice
    ++ (encodeUIntLE 8 message.clearingTradePrice
    ++ (encodeUIntLE 4 message.packageId
    ++ (encodeUIntLE 4 message.sideMarketSegmentId
    ++ (encodeUIntLE 2 message.sideTrdSubTyp
    ++ (encodeUInt 1 message.productComplex
    ++ (encodeUInt 1 message.tradePublishIndicator
    ++ (encodeUInt 1 message.instrmtMatchSideId
    ++ (encodeUInt 1 message.effectOnBasket
    ++ (Alpha.encode message.tradeReportText
    ++ (Alpha.encode message.pad6)))))))))))))

def decode (bytes : List UInt8) : Option (InstrmtMatchSideGrpComp × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  let (transBkdTime, bytes) ← decodeUIntLE 8 bytes
  let (relatedClosePrice, bytes) ← decodeUIntLE 8 bytes
  let (clearingTradePrice, bytes) ← decodeUIntLE 8 bytes
  let (packageId, bytes) ← decodeUIntLE 4 bytes
  let (sideMarketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (sideTrdSubTyp, bytes) ← decodeUIntLE 2 bytes
  let (productComplex, bytes) ← decodeUInt 1 bytes
  let (tradePublishIndicator, bytes) ← decodeUInt 1 bytes
  let (instrmtMatchSideId, bytes) ← decodeUInt 1 bytes
  let (effectOnBasket, bytes) ← decodeUInt 1 bytes
  let (tradeReportText, bytes) ← Alpha.decode 20 bytes
  let (pad6, bytes) ← Alpha.decode 6 bytes
  pure ({ securityId, lastPx, transBkdTime, relatedClosePrice, clearingTradePrice, packageId, sideMarketSegmentId, sideTrdSubTyp, productComplex, tradePublishIndicator, instrmtMatchSideId, effectOnBasket, tradeReportText, pad6 }, bytes)

@[simp] theorem encode_length (message : InstrmtMatchSideGrpComp) : (encode message).length = 80 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : InstrmtMatchSideGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstrmtMatchSideGrpComp) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end InstrmtMatchSideGrpComp

/-- Basket Side Alloc Grp Comp: 32 bytes -/
structure BasketSideAllocGrpComp where
  allocQty : BitVec 64
  individualAllocId : BitVec 32
  partySubIdType : BitVec 16
  side : BitVec 8
  instrmtMatchSideId : BitVec 8
  tradeAllocStatus : BitVec 8
  partyExecutingFirm : Alpha 5
  partyExecutingTrader : Alpha 6
  pad4 : Alpha 4
  deriving DecidableEq, Repr

namespace BasketSideAllocGrpComp

def encode (message : BasketSideAllocGrpComp) : List UInt8 :=
  encodeUIntLE 8 message.allocQty
    ++ (encodeUIntLE 4 message.individualAllocId
    ++ (encodeUIntLE 2 message.partySubIdType
    ++ (encodeUInt 1 message.side
    ++ (encodeUInt 1 message.instrmtMatchSideId
    ++ (encodeUInt 1 message.tradeAllocStatus
    ++ (Alpha.encode message.partyExecutingFirm
    ++ (Alpha.encode message.partyExecutingTrader
    ++ (Alpha.encode message.pad4))))))))

def decode (bytes : List UInt8) : Option (BasketSideAllocGrpComp × List UInt8) := do
  let (allocQty, bytes) ← decodeUIntLE 8 bytes
  let (individualAllocId, bytes) ← decodeUIntLE 4 bytes
  let (partySubIdType, bytes) ← decodeUIntLE 2 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (instrmtMatchSideId, bytes) ← decodeUInt 1 bytes
  let (tradeAllocStatus, bytes) ← decodeUInt 1 bytes
  let (partyExecutingFirm, bytes) ← Alpha.decode 5 bytes
  let (partyExecutingTrader, bytes) ← Alpha.decode 6 bytes
  let (pad4, bytes) ← Alpha.decode 4 bytes
  pure ({ allocQty, individualAllocId, partySubIdType, side, instrmtMatchSideId, tradeAllocStatus, partyExecutingFirm, partyExecutingTrader, pad4 }, bytes)

@[simp] theorem encode_length (message : BasketSideAllocGrpComp) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : BasketSideAllocGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BasketSideAllocGrpComp) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end BasketSideAllocGrpComp

/-- Amend Basket Trade Request -/
structure AmendBasketTradeRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  basketTrdMatchId : BitVec 64
  basketExecId : BitVec 32
  marketSegmentId : BitVec 32
  maturityMonthYear : BitVec 32
  basketProfileId : BitVec 32
  trdType : BitVec 16
  tradeReportType : BitVec 8
  basketTradeReportType : BitVec 8
  basketTradeReportText : Alpha 20
  tradeReportId : Alpha 20
  basketRootPartyGrpComp : Bounded 1 BasketRootPartyGrpComp
  instrmtMatchSideGrpComp : Bounded 1 InstrmtMatchSideGrpComp
  basketSideAllocGrpComp : Bounded 2 BasketSideAllocGrpComp
  deriving DecidableEq, Repr

namespace AmendBasketTradeRequest

def encode (message : AmendBasketTradeRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 8 message.basketTrdMatchId
    ++ (encodeUIntLE 4 message.basketExecId
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.maturityMonthYear
    ++ (encodeUIntLE 4 message.basketProfileId
    ++ (encodeUIntLE 2 message.trdType
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.basketSideAllocGrpComp.val.length)
    ++ (encodeUInt 1 message.tradeReportType
    ++ (encodeUInt 1 message.basketTradeReportType
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.basketRootPartyGrpComp.val.length)
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.instrmtMatchSideGrpComp.val.length)
    ++ (Alpha.encode message.basketTradeReportText
    ++ (Alpha.encode message.tradeReportId
    ++ (encodeMany BasketRootPartyGrpComp.encode message.basketRootPartyGrpComp.val
    ++ (encodeMany InstrmtMatchSideGrpComp.encode message.instrmtMatchSideGrpComp.val
    ++ (encodeMany BasketSideAllocGrpComp.encode message.basketSideAllocGrpComp.val))))))))))))))))))

def decode (bytes : List UInt8) : Option (AmendBasketTradeRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (basketTrdMatchId, bytes) ← decodeUIntLE 8 bytes
  let (basketExecId, bytes) ← decodeUIntLE 4 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (maturityMonthYear, bytes) ← decodeUIntLE 4 bytes
  let (basketProfileId, bytes) ← decodeUIntLE 4 bytes
  let (trdType, bytes) ← decodeUIntLE 2 bytes
  let (noBasketSideAlloc, bytes) ← decodeUIntLE 2 bytes
  let (tradeReportType, bytes) ← decodeUInt 1 bytes
  let (basketTradeReportType, bytes) ← decodeUInt 1 bytes
  let (noBasketRootPartyGrps, bytes) ← decodeUInt 1 bytes
  let (noInstrmtMatchSides, bytes) ← decodeUInt 1 bytes
  let (basketTradeReportText, bytes) ← Alpha.decode 20 bytes
  let (tradeReportId, bytes) ← Alpha.decode 20 bytes
  let (basketRootPartyGrpComp_, bytes) ← decodeMany BasketRootPartyGrpComp.decode noBasketRootPartyGrps.toNat bytes
  let (instrmtMatchSideGrpComp_, bytes) ← decodeMany InstrmtMatchSideGrpComp.decode noInstrmtMatchSides.toNat bytes
  let (basketSideAllocGrpComp_, bytes) ← decodeMany BasketSideAllocGrpComp.decode noBasketSideAlloc.toNat bytes
  if fits_basketRootPartyGrpComp : basketRootPartyGrpComp_.length < 256 ^ 1 then
    if fits_instrmtMatchSideGrpComp : instrmtMatchSideGrpComp_.length < 256 ^ 1 then
      if fits_basketSideAllocGrpComp : basketSideAllocGrpComp_.length < 256 ^ 2 then
        pure ({ networkMsgId, pad2, requestHeaderComp, basketTrdMatchId, basketExecId, marketSegmentId, maturityMonthYear, basketProfileId, trdType, tradeReportType, basketTradeReportType, basketTradeReportText, tradeReportId, basketRootPartyGrpComp := ⟨basketRootPartyGrpComp_, fits_basketRootPartyGrpComp⟩, instrmtMatchSideGrpComp := ⟨instrmtMatchSideGrpComp_, fits_instrmtMatchSideGrpComp⟩, basketSideAllocGrpComp := ⟨basketSideAllocGrpComp_, fits_basketSideAllocGrpComp⟩ }, bytes)
      else none
    else none
  else none

theorem encode_length_pos (message : AmendBasketTradeRequest) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : AmendBasketTradeRequest) : (encode message).length ≤ 2127810 := by
  have bound_basketRootPartyGrpComp := message.basketRootPartyGrpComp.length_lt
  have bound_instrmtMatchSideGrpComp := message.instrmtMatchSideGrpComp.length_lt
  have bound_basketSideAllocGrpComp := message.basketSideAllocGrpComp.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const BasketRootPartyGrpComp.encode 40 BasketRootPartyGrpComp.encode_length, encodeMany_length_const InstrmtMatchSideGrpComp.encode 80 InstrmtMatchSideGrpComp.encode_length, encodeMany_length_const BasketSideAllocGrpComp.encode 32 BasketSideAllocGrpComp.encode_length]
  omega

@[simp] theorem decode_encode (message : AmendBasketTradeRequest) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeMany_bounded 1 BasketRootPartyGrpComp.encode BasketRootPartyGrpComp.decode BasketRootPartyGrpComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeMany_bounded 1 InstrmtMatchSideGrpComp.encode InstrmtMatchSideGrpComp.decode InstrmtMatchSideGrpComp.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 BasketSideAllocGrpComp.encode BasketSideAllocGrpComp.decode BasketSideAllocGrpComp.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.basketRootPartyGrpComp.length_lt, dite_eq_left message.instrmtMatchSideGrpComp.length_lt, dite_eq_left message.basketSideAllocGrpComp.length_lt]
  rfl

end AmendBasketTradeRequest

/-- Basket Side Alloc Ext Grp Comp: 184 bytes -/
structure BasketSideAllocExtGrpComp where
  allocQty : BitVec 64
  partyIdClientId : BitVec 64
  partyIdInvestmentDecisionMaker : BitVec 64
  executingTrader : BitVec 64
  packageId : BitVec 32
  sideMarketSegmentId : BitVec 32
  allocId : BitVec 32
  side : BitVec 8
  positionEffect : PositionEffect
  tradingCapacity : BitVec 8
  orderAttributeLiquidityProvision : BitVec 8
  executingTraderQualifier : BitVec 8
  partyIdInvestmentDecisionMakerQualifier : BitVec 8
  orderAttributeRiskReduction : BitVec 8
  orderOrigination : BitVec 8
  partyExecutingFirm : Alpha 5
  partyExecutingTrader : Alpha 6
  account : Alpha 2
  freeText1 : Alpha 12
  freeText2 : Alpha 12
  freeText3 : Alpha 12
  partyIdTakeUpTradingFirm : Alpha 5
  partyIdOrderOriginationFirm : Alpha 7
  partyIdBeneficiary : Alpha 9
  partyIdPositionAccount : Alpha 32
  partyIdLocationId : Alpha 2
  custOrderHandlingInst : CustOrderHandlingInst
  complianceText : Alpha 20
  pad7 : Alpha 7
  deriving DecidableEq, Repr

namespace BasketSideAllocExtGrpComp

def encode (message : BasketSideAllocExtGrpComp) : List UInt8 :=
  encodeUIntLE 8 message.allocQty
    ++ (encodeUIntLE 8 message.partyIdClientId
    ++ (encodeUIntLE 8 message.partyIdInvestmentDecisionMaker
    ++ (encodeUIntLE 8 message.executingTrader
    ++ (encodeUIntLE 4 message.packageId
    ++ (encodeUIntLE 4 message.sideMarketSegmentId
    ++ (encodeUIntLE 4 message.allocId
    ++ (encodeUInt 1 message.side
    ++ (PositionEffect.encode message.positionEffect
    ++ (encodeUInt 1 message.tradingCapacity
    ++ (encodeUInt 1 message.orderAttributeLiquidityProvision
    ++ (encodeUInt 1 message.executingTraderQualifier
    ++ (encodeUInt 1 message.partyIdInvestmentDecisionMakerQualifier
    ++ (encodeUInt 1 message.orderAttributeRiskReduction
    ++ (encodeUInt 1 message.orderOrigination
    ++ (Alpha.encode message.partyExecutingFirm
    ++ (Alpha.encode message.partyExecutingTrader
    ++ (Alpha.encode message.account
    ++ (Alpha.encode message.freeText1
    ++ (Alpha.encode message.freeText2
    ++ (Alpha.encode message.freeText3
    ++ (Alpha.encode message.partyIdTakeUpTradingFirm
    ++ (Alpha.encode message.partyIdOrderOriginationFirm
    ++ (Alpha.encode message.partyIdBeneficiary
    ++ (Alpha.encode message.partyIdPositionAccount
    ++ (Alpha.encode message.partyIdLocationId
    ++ (CustOrderHandlingInst.encode message.custOrderHandlingInst
    ++ (Alpha.encode message.complianceText
    ++ (Alpha.encode message.pad7))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (BasketSideAllocExtGrpComp × List UInt8) := do
  let (allocQty, bytes) ← decodeUIntLE 8 bytes
  let (partyIdClientId, bytes) ← decodeUIntLE 8 bytes
  let (partyIdInvestmentDecisionMaker, bytes) ← decodeUIntLE 8 bytes
  let (executingTrader, bytes) ← decodeUIntLE 8 bytes
  let (packageId, bytes) ← decodeUIntLE 4 bytes
  let (sideMarketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (allocId, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (positionEffect, bytes) ← PositionEffect.decode bytes
  let (tradingCapacity, bytes) ← decodeUInt 1 bytes
  let (orderAttributeLiquidityProvision, bytes) ← decodeUInt 1 bytes
  let (executingTraderQualifier, bytes) ← decodeUInt 1 bytes
  let (partyIdInvestmentDecisionMakerQualifier, bytes) ← decodeUInt 1 bytes
  let (orderAttributeRiskReduction, bytes) ← decodeUInt 1 bytes
  let (orderOrigination, bytes) ← decodeUInt 1 bytes
  let (partyExecutingFirm, bytes) ← Alpha.decode 5 bytes
  let (partyExecutingTrader, bytes) ← Alpha.decode 6 bytes
  let (account, bytes) ← Alpha.decode 2 bytes
  let (freeText1, bytes) ← Alpha.decode 12 bytes
  let (freeText2, bytes) ← Alpha.decode 12 bytes
  let (freeText3, bytes) ← Alpha.decode 12 bytes
  let (partyIdTakeUpTradingFirm, bytes) ← Alpha.decode 5 bytes
  let (partyIdOrderOriginationFirm, bytes) ← Alpha.decode 7 bytes
  let (partyIdBeneficiary, bytes) ← Alpha.decode 9 bytes
  let (partyIdPositionAccount, bytes) ← Alpha.decode 32 bytes
  let (partyIdLocationId, bytes) ← Alpha.decode 2 bytes
  let (custOrderHandlingInst, bytes) ← CustOrderHandlingInst.decode bytes
  let (complianceText, bytes) ← Alpha.decode 20 bytes
  let (pad7, bytes) ← Alpha.decode 7 bytes
  pure ({ allocQty, partyIdClientId, partyIdInvestmentDecisionMaker, executingTrader, packageId, sideMarketSegmentId, allocId, side, positionEffect, tradingCapacity, orderAttributeLiquidityProvision, executingTraderQualifier, partyIdInvestmentDecisionMakerQualifier, orderAttributeRiskReduction, orderOrigination, partyExecutingFirm, partyExecutingTrader, account, freeText1, freeText2, freeText3, partyIdTakeUpTradingFirm, partyIdOrderOriginationFirm, partyIdBeneficiary, partyIdPositionAccount, partyIdLocationId, custOrderHandlingInst, complianceText, pad7 }, bytes)

@[simp] theorem encode_length (message : BasketSideAllocExtGrpComp) : (encode message).length = 184 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, PositionEffect.encode_length, Alpha.encode_length, CustOrderHandlingInst.encode_length]

theorem encode_length_pos (message : BasketSideAllocExtGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : BasketSideAllocExtGrpComp) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, PositionEffect.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CustOrderHandlingInst.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end BasketSideAllocExtGrpComp

/-- Approve Basket Trade Request -/
structure ApproveBasketTradeRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  basketTrdMatchId : BitVec 64
  basketExecId : BitVec 32
  marketSegmentId : BitVec 32
  rootPartySubIdType : BitVec 16
  trdType : BitVec 16
  tradeReportType : BitVec 8
  basketTradeReportText : Alpha 20
  tradeReportId : Alpha 20
  basketSideTradeReportId : Alpha 20
  pad5 : Alpha 5
  basketSideAllocExtGrpComp : Bounded 2 BasketSideAllocExtGrpComp
  deriving DecidableEq, Repr

namespace ApproveBasketTradeRequest

def encode (message : ApproveBasketTradeRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 8 message.basketTrdMatchId
    ++ (encodeUIntLE 4 message.basketExecId
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 2 message.rootPartySubIdType
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.basketSideAllocExtGrpComp.val.length)
    ++ (encodeUIntLE 2 message.trdType
    ++ (encodeUInt 1 message.tradeReportType
    ++ (Alpha.encode message.basketTradeReportText
    ++ (Alpha.encode message.tradeReportId
    ++ (Alpha.encode message.basketSideTradeReportId
    ++ (Alpha.encode message.pad5
    ++ (encodeMany BasketSideAllocExtGrpComp.encode message.basketSideAllocExtGrpComp.val))))))))))))))

def decode (bytes : List UInt8) : Option (ApproveBasketTradeRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (basketTrdMatchId, bytes) ← decodeUIntLE 8 bytes
  let (basketExecId, bytes) ← decodeUIntLE 4 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (rootPartySubIdType, bytes) ← decodeUIntLE 2 bytes
  let (noBasketSideAlloc, bytes) ← decodeUIntLE 2 bytes
  let (trdType, bytes) ← decodeUIntLE 2 bytes
  let (tradeReportType, bytes) ← decodeUInt 1 bytes
  let (basketTradeReportText, bytes) ← Alpha.decode 20 bytes
  let (tradeReportId, bytes) ← Alpha.decode 20 bytes
  let (basketSideTradeReportId, bytes) ← Alpha.decode 20 bytes
  let (pad5, bytes) ← Alpha.decode 5 bytes
  let (basketSideAllocExtGrpComp_, bytes) ← decodeMany BasketSideAllocExtGrpComp.decode noBasketSideAlloc.toNat bytes
  if fits_basketSideAllocExtGrpComp : basketSideAllocExtGrpComp_.length < 256 ^ 2 then
    pure ({ networkMsgId, pad2, requestHeaderComp, basketTrdMatchId, basketExecId, marketSegmentId, rootPartySubIdType, trdType, tradeReportType, basketTradeReportText, tradeReportId, basketSideTradeReportId, pad5, basketSideAllocExtGrpComp := ⟨basketSideAllocExtGrpComp_, fits_basketSideAllocExtGrpComp⟩ }, bytes)
  else none

theorem encode_length_pos (message : ApproveBasketTradeRequest) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ApproveBasketTradeRequest) : (encode message).length ≤ 12058546 := by
  have bound_basketSideAllocExtGrpComp := message.basketSideAllocExtGrpComp.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const BasketSideAllocExtGrpComp.encode 184 BasketSideAllocExtGrpComp.encode_length]
  omega

@[simp] theorem decode_encode (message : ApproveBasketTradeRequest) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 BasketSideAllocExtGrpComp.encode BasketSideAllocExtGrpComp.decode BasketSideAllocExtGrpComp.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.basketSideAllocExtGrpComp.length_lt]
  rfl

end ApproveBasketTradeRequest

/-- Approve Reverse Tes Trade Request: 66 bytes -/
structure ApproveReverseTesTradeRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  marketSegmentId : BitVec 32
  packageId : BitVec 32
  allocId : BitVec 32
  tesExecId : BitVec 32
  relatedMarketSegmentId : BitVec 32
  trdType : BitVec 16
  tradeReportId : Alpha 20
  pad6 : Alpha 6
  deriving DecidableEq, Repr

namespace ApproveReverseTesTradeRequest

def encode (message : ApproveReverseTesTradeRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.packageId
    ++ (encodeUIntLE 4 message.allocId
    ++ (encodeUIntLE 4 message.tesExecId
    ++ (encodeUIntLE 4 message.relatedMarketSegmentId
    ++ (encodeUIntLE 2 message.trdType
    ++ (Alpha.encode message.tradeReportId
    ++ (Alpha.encode message.pad6))))))))))

def decode (bytes : List UInt8) : Option (ApproveReverseTesTradeRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (packageId, bytes) ← decodeUIntLE 4 bytes
  let (allocId, bytes) ← decodeUIntLE 4 bytes
  let (tesExecId, bytes) ← decodeUIntLE 4 bytes
  let (relatedMarketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (trdType, bytes) ← decodeUIntLE 2 bytes
  let (tradeReportId, bytes) ← Alpha.decode 20 bytes
  let (pad6, bytes) ← Alpha.decode 6 bytes
  pure ({ networkMsgId, pad2, requestHeaderComp, marketSegmentId, packageId, allocId, tesExecId, relatedMarketSegmentId, trdType, tradeReportId, pad6 }, bytes)

@[simp] theorem encode_length (message : ApproveReverseTesTradeRequest) : (encode message).length = 66 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : ApproveReverseTesTradeRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ApproveReverseTesTradeRequest) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end ApproveReverseTesTradeRequest

/-- Approve Tes Trade Request: 250 bytes -/
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
  relatedMarketSegmentId : BitVec 32
  trdType : BitVec 16
  tradingCapacity : BitVec 8
  tradeReportType : BitVec 8
  side : BitVec 8
  orderAttributeLiquidityProvision : BitVec 8
  partyIdInvestmentDecisionMakerQualifier : BitVec 8
  executingTraderQualifier : BitVec 8
  orderAttributeRiskReduction : BitVec 8
  orderOrigination : BitVec 8
  tradeReportId : Alpha 20
  positionEffect : PositionEffect
  partyExecutingFirm : Alpha 5
  partyExecutingTrader : Alpha 6
  account : Alpha 2
  freeText1 : Alpha 12
  freeText2 : Alpha 12
  freeText3 : Alpha 12
  partyIdTakeUpTradingFirm : Alpha 5
  partyIdPositionAccount : Alpha 32
  partyIdOrderOriginationFirm : Alpha 7
  partyIdBeneficiary : Alpha 9
  partyIdLocationId : Alpha 2
  custOrderHandlingInst : CustOrderHandlingInst
  complianceText : Alpha 20
  partyEndClientIdentification : Alpha 20
  pad4 : Alpha 4
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
    ++ (encodeUIntLE 4 message.relatedMarketSegmentId
    ++ (encodeUIntLE 2 message.trdType
    ++ (encodeUInt 1 message.tradingCapacity
    ++ (encodeUInt 1 message.tradeReportType
    ++ (encodeUInt 1 message.side
    ++ (encodeUInt 1 message.orderAttributeLiquidityProvision
    ++ (encodeUInt 1 message.partyIdInvestmentDecisionMakerQualifier
    ++ (encodeUInt 1 message.executingTraderQualifier
    ++ (encodeUInt 1 message.orderAttributeRiskReduction
    ++ (encodeUInt 1 message.orderOrigination
    ++ (Alpha.encode message.tradeReportId
    ++ (PositionEffect.encode message.positionEffect
    ++ (Alpha.encode message.partyExecutingFirm
    ++ (Alpha.encode message.partyExecutingTrader
    ++ (Alpha.encode message.account
    ++ (Alpha.encode message.freeText1
    ++ (Alpha.encode message.freeText2
    ++ (Alpha.encode message.freeText3
    ++ (Alpha.encode message.partyIdTakeUpTradingFirm
    ++ (Alpha.encode message.partyIdPositionAccount
    ++ (Alpha.encode message.partyIdOrderOriginationFirm
    ++ (Alpha.encode message.partyIdBeneficiary
    ++ (Alpha.encode message.partyIdLocationId
    ++ (CustOrderHandlingInst.encode message.custOrderHandlingInst
    ++ (Alpha.encode message.complianceText
    ++ (Alpha.encode message.partyEndClientIdentification
    ++ (Alpha.encode message.pad4)))))))))))))))))))))))))))))))))))))

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
  let (relatedMarketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (trdType, bytes) ← decodeUIntLE 2 bytes
  let (tradingCapacity, bytes) ← decodeUInt 1 bytes
  let (tradeReportType, bytes) ← decodeUInt 1 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (orderAttributeLiquidityProvision, bytes) ← decodeUInt 1 bytes
  let (partyIdInvestmentDecisionMakerQualifier, bytes) ← decodeUInt 1 bytes
  let (executingTraderQualifier, bytes) ← decodeUInt 1 bytes
  let (orderAttributeRiskReduction, bytes) ← decodeUInt 1 bytes
  let (orderOrigination, bytes) ← decodeUInt 1 bytes
  let (tradeReportId, bytes) ← Alpha.decode 20 bytes
  let (positionEffect, bytes) ← PositionEffect.decode bytes
  let (partyExecutingFirm, bytes) ← Alpha.decode 5 bytes
  let (partyExecutingTrader, bytes) ← Alpha.decode 6 bytes
  let (account, bytes) ← Alpha.decode 2 bytes
  let (freeText1, bytes) ← Alpha.decode 12 bytes
  let (freeText2, bytes) ← Alpha.decode 12 bytes
  let (freeText3, bytes) ← Alpha.decode 12 bytes
  let (partyIdTakeUpTradingFirm, bytes) ← Alpha.decode 5 bytes
  let (partyIdPositionAccount, bytes) ← Alpha.decode 32 bytes
  let (partyIdOrderOriginationFirm, bytes) ← Alpha.decode 7 bytes
  let (partyIdBeneficiary, bytes) ← Alpha.decode 9 bytes
  let (partyIdLocationId, bytes) ← Alpha.decode 2 bytes
  let (custOrderHandlingInst, bytes) ← CustOrderHandlingInst.decode bytes
  let (complianceText, bytes) ← Alpha.decode 20 bytes
  let (partyEndClientIdentification, bytes) ← Alpha.decode 20 bytes
  let (pad4, bytes) ← Alpha.decode 4 bytes
  pure ({ networkMsgId, pad2, requestHeaderComp, partyIdClientId, partyIdInvestmentDecisionMaker, executingTrader, allocQty, packageId, allocId, tesExecId, marketSegmentId, relatedMarketSegmentId, trdType, tradingCapacity, tradeReportType, side, orderAttributeLiquidityProvision, partyIdInvestmentDecisionMakerQualifier, executingTraderQualifier, orderAttributeRiskReduction, orderOrigination, tradeReportId, positionEffect, partyExecutingFirm, partyExecutingTrader, account, freeText1, freeText2, freeText3, partyIdTakeUpTradingFirm, partyIdPositionAccount, partyIdOrderOriginationFirm, partyIdBeneficiary, partyIdLocationId, custOrderHandlingInst, complianceText, partyEndClientIdentification, pad4 }, bytes)

@[simp] theorem encode_length (message : ApproveTesTradeRequest) : (encode message).length = 250 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length, PositionEffect.encode_length, CustOrderHandlingInst.encode_length]

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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PositionEffect.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CustOrderHandlingInst.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ApproveTesTradeRequest

/-- Cross Request: 58 bytes -/
structure CrossRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  securityId : BitVec 64
  orderQty : BitVec 64
  marketSegmentId : BitVec 32
  complianceText : Alpha 20
  deriving DecidableEq, Repr

namespace CrossRequest

def encode (message : CrossRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.orderQty
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (Alpha.encode message.complianceText))))))

def decode (bytes : List UInt8) : Option (CrossRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (orderQty, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (complianceText, bytes) ← Alpha.decode 20 bytes
  pure ({ networkMsgId, pad2, requestHeaderComp, securityId, orderQty, marketSegmentId, complianceText }, bytes)

@[simp] theorem encode_length (message : CrossRequest) : (encode message).length = 58 := by
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

/-- Delete Basket Trade Request: 58 bytes -/
structure DeleteBasketTradeRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  basketTrdMatchId : BitVec 64
  basketExecId : BitVec 32
  marketSegmentId : BitVec 32
  trdType : BitVec 16
  tradeReportType : BitVec 8
  tradeReportId : Alpha 20
  pad1 : Alpha 1
  deriving DecidableEq, Repr

namespace DeleteBasketTradeRequest

def encode (message : DeleteBasketTradeRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 8 message.basketTrdMatchId
    ++ (encodeUIntLE 4 message.basketExecId
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 2 message.trdType
    ++ (encodeUInt 1 message.tradeReportType
    ++ (Alpha.encode message.tradeReportId
    ++ (Alpha.encode message.pad1)))))))))

def decode (bytes : List UInt8) : Option (DeleteBasketTradeRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (basketTrdMatchId, bytes) ← decodeUIntLE 8 bytes
  let (basketExecId, bytes) ← decodeUIntLE 4 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (trdType, bytes) ← decodeUIntLE 2 bytes
  let (tradeReportType, bytes) ← decodeUInt 1 bytes
  let (tradeReportId, bytes) ← Alpha.decode 20 bytes
  let (pad1, bytes) ← Alpha.decode 1 bytes
  pure ({ networkMsgId, pad2, requestHeaderComp, basketTrdMatchId, basketExecId, marketSegmentId, trdType, tradeReportType, tradeReportId, pad1 }, bytes)

@[simp] theorem encode_length (message : DeleteBasketTradeRequest) : (encode message).length = 58 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : DeleteBasketTradeRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DeleteBasketTradeRequest) (rest : List UInt8) :
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

end DeleteBasketTradeRequest

/-- Delete Clip Request: 66 bytes -/
structure DeleteClipRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  orderId : BitVec 64
  securityId : BitVec 64
  partyIdInvestmentDecisionMaker : BitVec 64
  executingTrader : BitVec 64
  marketSegmentId : BitVec 32
  crossRequestId : BitVec 32
  executingTraderQualifier : BitVec 8
  partyIdInvestmentDecisionMakerQualifier : BitVec 8
  pad6 : Alpha 6
  deriving DecidableEq, Repr

namespace DeleteClipRequest

def encode (message : DeleteClipRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.partyIdInvestmentDecisionMaker
    ++ (encodeUIntLE 8 message.executingTrader
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.crossRequestId
    ++ (encodeUInt 1 message.executingTraderQualifier
    ++ (encodeUInt 1 message.partyIdInvestmentDecisionMakerQualifier
    ++ (Alpha.encode message.pad6)))))))))))

def decode (bytes : List UInt8) : Option (DeleteClipRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (partyIdInvestmentDecisionMaker, bytes) ← decodeUIntLE 8 bytes
  let (executingTrader, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (crossRequestId, bytes) ← decodeUIntLE 4 bytes
  let (executingTraderQualifier, bytes) ← decodeUInt 1 bytes
  let (partyIdInvestmentDecisionMakerQualifier, bytes) ← decodeUInt 1 bytes
  let (pad6, bytes) ← Alpha.decode 6 bytes
  pure ({ networkMsgId, pad2, requestHeaderComp, orderId, securityId, partyIdInvestmentDecisionMaker, executingTrader, marketSegmentId, crossRequestId, executingTraderQualifier, partyIdInvestmentDecisionMakerQualifier, pad6 }, bytes)

@[simp] theorem encode_length (message : DeleteClipRequest) : (encode message).length = 66 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : DeleteClipRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DeleteClipRequest) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end DeleteClipRequest

/-- Delete Order Complex Request: 122 bytes -/
structure DeleteOrderComplexRequest where
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
  complianceText : Alpha 20
  pad5 : Alpha 5
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
    ++ (encodeUIntLE 8 message.partyIdInvestmentDecisionMaker
    ++ (encodeUIntLE 8 message.executingTrader
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.targetPartyIdSessionId
    ++ (encodeUInt 1 message.orderOrigination
    ++ (encodeUInt 1 message.partyIdInvestmentDecisionMakerQualifier
    ++ (encodeUInt 1 message.executingTraderQualifier
    ++ (Alpha.encode message.fixClOrdId
    ++ (Alpha.encode message.complianceText
    ++ (Alpha.encode message.pad5))))))))))))))))

def decode (bytes : List UInt8) : Option (DeleteOrderComplexRequest × List UInt8) := do
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
  let (complianceText, bytes) ← Alpha.decode 20 bytes
  let (pad5, bytes) ← Alpha.decode 5 bytes
  pure ({ networkMsgId, pad2, requestHeaderComp, orderId, clOrdId, origClOrdId, securityId, partyIdInvestmentDecisionMaker, executingTrader, marketSegmentId, targetPartyIdSessionId, orderOrigination, partyIdInvestmentDecisionMakerQualifier, executingTraderQualifier, fixClOrdId, complianceText, pad5 }, bytes)

@[simp] theorem encode_length (message : DeleteOrderComplexRequest) : (encode message).length = 122 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length]

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
  rw [Alpha.decode_encode, some_bind]
  rfl

end DeleteOrderComplexRequest

/-- Delete Order Request: 122 bytes -/
structure DeleteOrderRequest where
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
  complianceText : Alpha 20
  pad5 : Alpha 5
  deriving DecidableEq, Repr

namespace DeleteOrderRequest

def encode (message : DeleteOrderRequest) : List UInt8 :=
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
    ++ (Alpha.encode message.complianceText
    ++ (Alpha.encode message.pad5))))))))))))))))

def decode (bytes : List UInt8) : Option (DeleteOrderRequest × List UInt8) := do
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
  let (complianceText, bytes) ← Alpha.decode 20 bytes
  let (pad5, bytes) ← Alpha.decode 5 bytes
  pure ({ networkMsgId, pad2, requestHeaderComp, orderId, clOrdId, origClOrdId, securityId, partyIdInvestmentDecisionMaker, executingTrader, marketSegmentId, targetPartyIdSessionId, orderOrigination, partyIdInvestmentDecisionMakerQualifier, executingTraderQualifier, fixClOrdId, complianceText, pad5 }, bytes)

@[simp] theorem encode_length (message : DeleteOrderRequest) : (encode message).length = 122 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : DeleteOrderRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DeleteOrderRequest) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end DeleteOrderRequest

/-- Delete Order Single Request: 122 bytes -/
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
  complianceText : Alpha 20
  pad5 : Alpha 5
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
    ++ (Alpha.encode message.complianceText
    ++ (Alpha.encode message.pad5))))))))))))))))

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
  let (complianceText, bytes) ← Alpha.decode 20 bytes
  let (pad5, bytes) ← Alpha.decode 5 bytes
  pure ({ networkMsgId, pad2, requestHeaderComp, orderId, clOrdId, origClOrdId, securityId, partyIdInvestmentDecisionMaker, executingTrader, marketSegmentId, targetPartyIdSessionId, orderOrigination, partyIdInvestmentDecisionMakerQualifier, executingTraderQualifier, fixClOrdId, complianceText, pad5 }, bytes)

@[simp] theorem encode_length (message : DeleteOrderSingleRequest) : (encode message).length = 122 := by
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
  relatedMarketSegmentId : BitVec 32
  trdType : BitVec 16
  tradeReportType : BitVec 8
  tradeReportId : Alpha 20
  pad1 : Alpha 1
  deriving DecidableEq, Repr

namespace DeleteTesTradeRequest

def encode (message : DeleteTesTradeRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 4 message.packageId
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.tesExecId
    ++ (encodeUIntLE 4 message.relatedMarketSegmentId
    ++ (encodeUIntLE 2 message.trdType
    ++ (encodeUInt 1 message.tradeReportType
    ++ (Alpha.encode message.tradeReportId
    ++ (Alpha.encode message.pad1))))))))))

def decode (bytes : List UInt8) : Option (DeleteTesTradeRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (packageId, bytes) ← decodeUIntLE 4 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (tesExecId, bytes) ← decodeUIntLE 4 bytes
  let (relatedMarketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (trdType, bytes) ← decodeUIntLE 2 bytes
  let (tradeReportType, bytes) ← decodeUInt 1 bytes
  let (tradeReportId, bytes) ← Alpha.decode 20 bytes
  let (pad1, bytes) ← Alpha.decode 1 bytes
  pure ({ networkMsgId, pad2, requestHeaderComp, packageId, marketSegmentId, tesExecId, relatedMarketSegmentId, trdType, tradeReportType, tradeReportId, pad1 }, bytes)

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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end DeleteTesTradeRequest

/-- Enter Basket Trade Request -/
structure EnterBasketTradeRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  marketSegmentId : BitVec 32
  maturityMonthYear : BitVec 32
  basketProfileId : BitVec 32
  trdType : BitVec 16
  tradeReportType : BitVec 8
  basketTradeReportType : BitVec 8
  basketAnonymity : BitVec 8
  basketTradeReportText : Alpha 20
  tradeReportId : Alpha 20
  pad3 : Alpha 3
  basketRootPartyGrpComp : Bounded 1 BasketRootPartyGrpComp
  instrmtMatchSideGrpComp : Bounded 1 InstrmtMatchSideGrpComp
  basketSideAllocGrpComp : Bounded 2 BasketSideAllocGrpComp
  deriving DecidableEq, Repr

namespace EnterBasketTradeRequest

def encode (message : EnterBasketTradeRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.maturityMonthYear
    ++ (encodeUIntLE 4 message.basketProfileId
    ++ (encodeUIntLE 2 message.trdType
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.basketSideAllocGrpComp.val.length)
    ++ (encodeUInt 1 message.tradeReportType
    ++ (encodeUInt 1 message.basketTradeReportType
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.basketRootPartyGrpComp.val.length)
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.instrmtMatchSideGrpComp.val.length)
    ++ (encodeUInt 1 message.basketAnonymity
    ++ (Alpha.encode message.basketTradeReportText
    ++ (Alpha.encode message.tradeReportId
    ++ (Alpha.encode message.pad3
    ++ (encodeMany BasketRootPartyGrpComp.encode message.basketRootPartyGrpComp.val
    ++ (encodeMany InstrmtMatchSideGrpComp.encode message.instrmtMatchSideGrpComp.val
    ++ (encodeMany BasketSideAllocGrpComp.encode message.basketSideAllocGrpComp.val))))))))))))))))))

def decode (bytes : List UInt8) : Option (EnterBasketTradeRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (maturityMonthYear, bytes) ← decodeUIntLE 4 bytes
  let (basketProfileId, bytes) ← decodeUIntLE 4 bytes
  let (trdType, bytes) ← decodeUIntLE 2 bytes
  let (noBasketSideAlloc, bytes) ← decodeUIntLE 2 bytes
  let (tradeReportType, bytes) ← decodeUInt 1 bytes
  let (basketTradeReportType, bytes) ← decodeUInt 1 bytes
  let (noBasketRootPartyGrps, bytes) ← decodeUInt 1 bytes
  let (noInstrmtMatchSides, bytes) ← decodeUInt 1 bytes
  let (basketAnonymity, bytes) ← decodeUInt 1 bytes
  let (basketTradeReportText, bytes) ← Alpha.decode 20 bytes
  let (tradeReportId, bytes) ← Alpha.decode 20 bytes
  let (pad3, bytes) ← Alpha.decode 3 bytes
  let (basketRootPartyGrpComp_, bytes) ← decodeMany BasketRootPartyGrpComp.decode noBasketRootPartyGrps.toNat bytes
  let (instrmtMatchSideGrpComp_, bytes) ← decodeMany InstrmtMatchSideGrpComp.decode noInstrmtMatchSides.toNat bytes
  let (basketSideAllocGrpComp_, bytes) ← decodeMany BasketSideAllocGrpComp.decode noBasketSideAlloc.toNat bytes
  if fits_basketRootPartyGrpComp : basketRootPartyGrpComp_.length < 256 ^ 1 then
    if fits_instrmtMatchSideGrpComp : instrmtMatchSideGrpComp_.length < 256 ^ 1 then
      if fits_basketSideAllocGrpComp : basketSideAllocGrpComp_.length < 256 ^ 2 then
        pure ({ networkMsgId, pad2, requestHeaderComp, marketSegmentId, maturityMonthYear, basketProfileId, trdType, tradeReportType, basketTradeReportType, basketAnonymity, basketTradeReportText, tradeReportId, pad3, basketRootPartyGrpComp := ⟨basketRootPartyGrpComp_, fits_basketRootPartyGrpComp⟩, instrmtMatchSideGrpComp := ⟨instrmtMatchSideGrpComp_, fits_instrmtMatchSideGrpComp⟩, basketSideAllocGrpComp := ⟨basketSideAllocGrpComp_, fits_basketSideAllocGrpComp⟩ }, bytes)
      else none
    else none
  else none

theorem encode_length_pos (message : EnterBasketTradeRequest) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : EnterBasketTradeRequest) : (encode message).length ≤ 2127802 := by
  have bound_basketRootPartyGrpComp := message.basketRootPartyGrpComp.length_lt
  have bound_instrmtMatchSideGrpComp := message.instrmtMatchSideGrpComp.length_lt
  have bound_basketSideAllocGrpComp := message.basketSideAllocGrpComp.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const BasketRootPartyGrpComp.encode 40 BasketRootPartyGrpComp.encode_length, encodeMany_length_const InstrmtMatchSideGrpComp.encode 80 InstrmtMatchSideGrpComp.encode_length, encodeMany_length_const BasketSideAllocGrpComp.encode 32 BasketSideAllocGrpComp.encode_length]
  omega

@[simp] theorem decode_encode (message : EnterBasketTradeRequest) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeMany_bounded 1 BasketRootPartyGrpComp.encode BasketRootPartyGrpComp.decode BasketRootPartyGrpComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeMany_bounded 1 InstrmtMatchSideGrpComp.encode InstrmtMatchSideGrpComp.decode InstrmtMatchSideGrpComp.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 BasketSideAllocGrpComp.encode BasketSideAllocGrpComp.decode BasketSideAllocGrpComp.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.basketRootPartyGrpComp.length_lt, dite_eq_left message.instrmtMatchSideGrpComp.length_lt, dite_eq_left message.basketSideAllocGrpComp.length_lt]
  rfl

end EnterBasketTradeRequest

/-- Cross Request Side Grp Comp: 184 bytes -/
structure CrossRequestSideGrpComp where
  partyIdClientId : BitVec 64
  partyIdInvestmentDecisionMaker : BitVec 64
  executingTrader : BitVec 64
  maximumPrice : BitVec 64
  matchInstCrossId : BitVec 32
  inputSource : BitVec 8
  side : BitVec 8
  selfMatchPreventionInstruction : BitVec 8
  tradingCapacity : BitVec 8
  executingTraderQualifier : BitVec 8
  orderAttributeLiquidityProvision : BitVec 8
  partyIdInvestmentDecisionMakerQualifier : BitVec 8
  orderAttributeRiskReduction : BitVec 8
  orderOrigination : BitVec 8
  positionEffect : PositionEffect
  custOrderHandlingInst : CustOrderHandlingInst
  account : Alpha 2
  partyIdPositionAccount : Alpha 32
  freeText1 : Alpha 12
  freeText2 : Alpha 12
  freeText3 : Alpha 12
  partyIdOrderOriginationFirm : Alpha 7
  partyIdBeneficiary : Alpha 9
  partyIdTakeUpTradingFirm : Alpha 5
  sideComplianceText : Alpha 20
  partyIdLocationId : Alpha 2
  partyEndClientIdentification : Alpha 20
  pad4 : Alpha 4
  deriving DecidableEq, Repr

namespace CrossRequestSideGrpComp

def encode (message : CrossRequestSideGrpComp) : List UInt8 :=
  encodeUIntLE 8 message.partyIdClientId
    ++ (encodeUIntLE 8 message.partyIdInvestmentDecisionMaker
    ++ (encodeUIntLE 8 message.executingTrader
    ++ (encodeUIntLE 8 message.maximumPrice
    ++ (encodeUIntLE 4 message.matchInstCrossId
    ++ (encodeUInt 1 message.inputSource
    ++ (encodeUInt 1 message.side
    ++ (encodeUInt 1 message.selfMatchPreventionInstruction
    ++ (encodeUInt 1 message.tradingCapacity
    ++ (encodeUInt 1 message.executingTraderQualifier
    ++ (encodeUInt 1 message.orderAttributeLiquidityProvision
    ++ (encodeUInt 1 message.partyIdInvestmentDecisionMakerQualifier
    ++ (encodeUInt 1 message.orderAttributeRiskReduction
    ++ (encodeUInt 1 message.orderOrigination
    ++ (PositionEffect.encode message.positionEffect
    ++ (CustOrderHandlingInst.encode message.custOrderHandlingInst
    ++ (Alpha.encode message.account
    ++ (Alpha.encode message.partyIdPositionAccount
    ++ (Alpha.encode message.freeText1
    ++ (Alpha.encode message.freeText2
    ++ (Alpha.encode message.freeText3
    ++ (Alpha.encode message.partyIdOrderOriginationFirm
    ++ (Alpha.encode message.partyIdBeneficiary
    ++ (Alpha.encode message.partyIdTakeUpTradingFirm
    ++ (Alpha.encode message.sideComplianceText
    ++ (Alpha.encode message.partyIdLocationId
    ++ (Alpha.encode message.partyEndClientIdentification
    ++ (Alpha.encode message.pad4)))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (CrossRequestSideGrpComp × List UInt8) := do
  let (partyIdClientId, bytes) ← decodeUIntLE 8 bytes
  let (partyIdInvestmentDecisionMaker, bytes) ← decodeUIntLE 8 bytes
  let (executingTrader, bytes) ← decodeUIntLE 8 bytes
  let (maximumPrice, bytes) ← decodeUIntLE 8 bytes
  let (matchInstCrossId, bytes) ← decodeUIntLE 4 bytes
  let (inputSource, bytes) ← decodeUInt 1 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (selfMatchPreventionInstruction, bytes) ← decodeUInt 1 bytes
  let (tradingCapacity, bytes) ← decodeUInt 1 bytes
  let (executingTraderQualifier, bytes) ← decodeUInt 1 bytes
  let (orderAttributeLiquidityProvision, bytes) ← decodeUInt 1 bytes
  let (partyIdInvestmentDecisionMakerQualifier, bytes) ← decodeUInt 1 bytes
  let (orderAttributeRiskReduction, bytes) ← decodeUInt 1 bytes
  let (orderOrigination, bytes) ← decodeUInt 1 bytes
  let (positionEffect, bytes) ← PositionEffect.decode bytes
  let (custOrderHandlingInst, bytes) ← CustOrderHandlingInst.decode bytes
  let (account, bytes) ← Alpha.decode 2 bytes
  let (partyIdPositionAccount, bytes) ← Alpha.decode 32 bytes
  let (freeText1, bytes) ← Alpha.decode 12 bytes
  let (freeText2, bytes) ← Alpha.decode 12 bytes
  let (freeText3, bytes) ← Alpha.decode 12 bytes
  let (partyIdOrderOriginationFirm, bytes) ← Alpha.decode 7 bytes
  let (partyIdBeneficiary, bytes) ← Alpha.decode 9 bytes
  let (partyIdTakeUpTradingFirm, bytes) ← Alpha.decode 5 bytes
  let (sideComplianceText, bytes) ← Alpha.decode 20 bytes
  let (partyIdLocationId, bytes) ← Alpha.decode 2 bytes
  let (partyEndClientIdentification, bytes) ← Alpha.decode 20 bytes
  let (pad4, bytes) ← Alpha.decode 4 bytes
  pure ({ partyIdClientId, partyIdInvestmentDecisionMaker, executingTrader, maximumPrice, matchInstCrossId, inputSource, side, selfMatchPreventionInstruction, tradingCapacity, executingTraderQualifier, orderAttributeLiquidityProvision, partyIdInvestmentDecisionMakerQualifier, orderAttributeRiskReduction, orderOrigination, positionEffect, custOrderHandlingInst, account, partyIdPositionAccount, freeText1, freeText2, freeText3, partyIdOrderOriginationFirm, partyIdBeneficiary, partyIdTakeUpTradingFirm, sideComplianceText, partyIdLocationId, partyEndClientIdentification, pad4 }, bytes)

@[simp] theorem encode_length (message : CrossRequestSideGrpComp) : (encode message).length = 184 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, PositionEffect.encode_length, CustOrderHandlingInst.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : CrossRequestSideGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : CrossRequestSideGrpComp) (rest : List UInt8) :
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
  rw [List.append_assoc, PositionEffect.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CustOrderHandlingInst.decode_encode, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end CrossRequestSideGrpComp

/-- Side Cross Leg Grp Comp: 8 bytes -/
structure SideCrossLegGrpComp where
  legInputSource : BitVec 8
  legPositionEffect : LegPositionEffect
  legAccount : Alpha 2
  pad4 : Alpha 4
  deriving DecidableEq, Repr

namespace SideCrossLegGrpComp

def encode (message : SideCrossLegGrpComp) : List UInt8 :=
  encodeUInt 1 message.legInputSource
    ++ (LegPositionEffect.encode message.legPositionEffect
    ++ (Alpha.encode message.legAccount
    ++ (Alpha.encode message.pad4)))

def decode (bytes : List UInt8) : Option (SideCrossLegGrpComp × List UInt8) := do
  let (legInputSource, bytes) ← decodeUInt 1 bytes
  let (legPositionEffect, bytes) ← LegPositionEffect.decode bytes
  let (legAccount, bytes) ← Alpha.decode 2 bytes
  let (pad4, bytes) ← Alpha.decode 4 bytes
  pure ({ legInputSource, legPositionEffect, legAccount, pad4 }, bytes)

@[simp] theorem encode_length (message : SideCrossLegGrpComp) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, LegPositionEffect.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : SideCrossLegGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SideCrossLegGrpComp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, LegPositionEffect.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SideCrossLegGrpComp

/-- Enter Clip Request -/
structure EnterClipRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  securityId : BitVec 64
  price : BitVec 64
  orderQty : BitVec 64
  marketSegmentId : BitVec 32
  crossId : BitVec 32
  crossRequestId : BitVec 32
  crossRequestType : BitVec 8
  crossType : BitVec 8
  crossPrioritization : BitVec 8
  sideDisclosureInstruction : BitVec 8
  priceDisclosureInstruction : BitVec 8
  orderQtyDisclosureInstruction : BitVec 8
  priceValidityCheckType : BitVec 8
  valueCheckTypeValue : BitVec 8
  rootPartyContraFirm : Alpha 5
  rootPartyContraTrader : Alpha 6
  pad7 : Alpha 7
  crossRequestSideGrpComp : Bounded 1 CrossRequestSideGrpComp
  sideCrossLegGrpComp : Bounded 1 SideCrossLegGrpComp
  deriving DecidableEq, Repr

namespace EnterClipRequest

def encode (message : EnterClipRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 8 message.orderQty
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.crossId
    ++ (encodeUIntLE 4 message.crossRequestId
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.crossRequestSideGrpComp.val.length)
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.sideCrossLegGrpComp.val.length)
    ++ (encodeUInt 1 message.crossRequestType
    ++ (encodeUInt 1 message.crossType
    ++ (encodeUInt 1 message.crossPrioritization
    ++ (encodeUInt 1 message.sideDisclosureInstruction
    ++ (encodeUInt 1 message.priceDisclosureInstruction
    ++ (encodeUInt 1 message.orderQtyDisclosureInstruction
    ++ (encodeUInt 1 message.priceValidityCheckType
    ++ (encodeUInt 1 message.valueCheckTypeValue
    ++ (Alpha.encode message.rootPartyContraFirm
    ++ (Alpha.encode message.rootPartyContraTrader
    ++ (Alpha.encode message.pad7
    ++ (encodeMany CrossRequestSideGrpComp.encode message.crossRequestSideGrpComp.val
    ++ (encodeMany SideCrossLegGrpComp.encode message.sideCrossLegGrpComp.val)))))))))))))))))))))))

def decode (bytes : List UInt8) : Option (EnterClipRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (orderQty, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (crossId, bytes) ← decodeUIntLE 4 bytes
  let (crossRequestId, bytes) ← decodeUIntLE 4 bytes
  let (noSides, bytes) ← decodeUInt 1 bytes
  let (noCrossLegs, bytes) ← decodeUInt 1 bytes
  let (crossRequestType, bytes) ← decodeUInt 1 bytes
  let (crossType, bytes) ← decodeUInt 1 bytes
  let (crossPrioritization, bytes) ← decodeUInt 1 bytes
  let (sideDisclosureInstruction, bytes) ← decodeUInt 1 bytes
  let (priceDisclosureInstruction, bytes) ← decodeUInt 1 bytes
  let (orderQtyDisclosureInstruction, bytes) ← decodeUInt 1 bytes
  let (priceValidityCheckType, bytes) ← decodeUInt 1 bytes
  let (valueCheckTypeValue, bytes) ← decodeUInt 1 bytes
  let (rootPartyContraFirm, bytes) ← Alpha.decode 5 bytes
  let (rootPartyContraTrader, bytes) ← Alpha.decode 6 bytes
  let (pad7, bytes) ← Alpha.decode 7 bytes
  let (crossRequestSideGrpComp_, bytes) ← decodeMany CrossRequestSideGrpComp.decode noSides.toNat bytes
  let (sideCrossLegGrpComp_, bytes) ← decodeMany SideCrossLegGrpComp.decode noCrossLegs.toNat bytes
  if fits_crossRequestSideGrpComp : crossRequestSideGrpComp_.length < 256 ^ 1 then
    if fits_sideCrossLegGrpComp : sideCrossLegGrpComp_.length < 256 ^ 1 then
      pure ({ networkMsgId, pad2, requestHeaderComp, securityId, price, orderQty, marketSegmentId, crossId, crossRequestId, crossRequestType, crossType, crossPrioritization, sideDisclosureInstruction, priceDisclosureInstruction, orderQtyDisclosureInstruction, priceValidityCheckType, valueCheckTypeValue, rootPartyContraFirm, rootPartyContraTrader, pad7, crossRequestSideGrpComp := ⟨crossRequestSideGrpComp_, fits_crossRequestSideGrpComp⟩, sideCrossLegGrpComp := ⟨sideCrossLegGrpComp_, fits_sideCrossLegGrpComp⟩ }, bytes)
    else none
  else none

theorem encode_length_pos (message : EnterClipRequest) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : EnterClipRequest) : (encode message).length ≤ 49042 := by
  have bound_crossRequestSideGrpComp := message.crossRequestSideGrpComp.length_lt
  have bound_sideCrossLegGrpComp := message.sideCrossLegGrpComp.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const CrossRequestSideGrpComp.encode 184 CrossRequestSideGrpComp.encode_length, encodeMany_length_const SideCrossLegGrpComp.encode 8 SideCrossLegGrpComp.encode_length]
  omega

@[simp] theorem decode_encode (message : EnterClipRequest) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeMany_bounded 1 CrossRequestSideGrpComp.encode CrossRequestSideGrpComp.decode CrossRequestSideGrpComp.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 SideCrossLegGrpComp.encode SideCrossLegGrpComp.decode SideCrossLegGrpComp.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.crossRequestSideGrpComp.length_lt, dite_eq_left message.sideCrossLegGrpComp.length_lt]
  rfl

end EnterClipRequest

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

/-- Trd Instrmnt Leg Grp Comp: 24 bytes -/
structure TrdInstrmntLegGrpComp where
  legSecurityId : BitVec 64
  legPrice : BitVec 64
  legQty : BitVec 64
  deriving DecidableEq, Repr

namespace TrdInstrmntLegGrpComp

def encode (message : TrdInstrmntLegGrpComp) : List UInt8 :=
  encodeUIntLE 8 message.legSecurityId
    ++ (encodeUIntLE 8 message.legPrice
    ++ (encodeUIntLE 8 message.legQty))

def decode (bytes : List UInt8) : Option (TrdInstrmntLegGrpComp × List UInt8) := do
  let (legSecurityId, bytes) ← decodeUIntLE 8 bytes
  let (legPrice, bytes) ← decodeUIntLE 8 bytes
  let (legQty, bytes) ← decodeUIntLE 8 bytes
  pure ({ legSecurityId, legPrice, legQty }, bytes)

@[simp] theorem encode_length (message : TrdInstrmntLegGrpComp) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : TrdInstrmntLegGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TrdInstrmntLegGrpComp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end TrdInstrmntLegGrpComp

/-- Instrument Event Grp Comp: 8 bytes -/
structure InstrumentEventGrpComp where
  eventDate : BitVec 32
  eventType : BitVec 8
  pad3 : Alpha 3
  deriving DecidableEq, Repr

namespace InstrumentEventGrpComp

def encode (message : InstrumentEventGrpComp) : List UInt8 :=
  encodeUIntLE 4 message.eventDate
    ++ (encodeUInt 1 message.eventType
    ++ (Alpha.encode message.pad3))

def decode (bytes : List UInt8) : Option (InstrumentEventGrpComp × List UInt8) := do
  let (eventDate, bytes) ← decodeUIntLE 4 bytes
  let (eventType, bytes) ← decodeUInt 1 bytes
  let (pad3, bytes) ← Alpha.decode 3 bytes
  pure ({ eventDate, eventType, pad3 }, bytes)

@[simp] theorem encode_length (message : InstrumentEventGrpComp) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : InstrumentEventGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstrumentEventGrpComp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end InstrumentEventGrpComp

/-- Instrument Attribute Grp Comp: 40 bytes -/
structure InstrumentAttributeGrpComp where
  instrAttribType : BitVec 8
  instrAttribValue : Alpha 32
  pad7 : Alpha 7
  deriving DecidableEq, Repr

namespace InstrumentAttributeGrpComp

def encode (message : InstrumentAttributeGrpComp) : List UInt8 :=
  encodeUInt 1 message.instrAttribType
    ++ (Alpha.encode message.instrAttribValue
    ++ (Alpha.encode message.pad7))

def decode (bytes : List UInt8) : Option (InstrumentAttributeGrpComp × List UInt8) := do
  let (instrAttribType, bytes) ← decodeUInt 1 bytes
  let (instrAttribValue, bytes) ← Alpha.decode 32 bytes
  let (pad7, bytes) ← Alpha.decode 7 bytes
  pure ({ instrAttribType, instrAttribValue, pad7 }, bytes)

@[simp] theorem encode_length (message : InstrumentAttributeGrpComp) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : InstrumentAttributeGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstrumentAttributeGrpComp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end InstrumentAttributeGrpComp

/-- Underlying Stip Grp Comp: 40 bytes -/
structure UnderlyingStipGrpComp where
  underlyingStipValue : Alpha 32
  underlyingStipType : Alpha 7
  pad1 : Alpha 1
  deriving DecidableEq, Repr

namespace UnderlyingStipGrpComp

def encode (message : UnderlyingStipGrpComp) : List UInt8 :=
  Alpha.encode message.underlyingStipValue
    ++ (Alpha.encode message.underlyingStipType
    ++ (Alpha.encode message.pad1))

def decode (bytes : List UInt8) : Option (UnderlyingStipGrpComp × List UInt8) := do
  let (underlyingStipValue, bytes) ← Alpha.decode 32 bytes
  let (underlyingStipType, bytes) ← Alpha.decode 7 bytes
  let (pad1, bytes) ← Alpha.decode 1 bytes
  pure ({ underlyingStipValue, underlyingStipType, pad1 }, bytes)

@[simp] theorem encode_length (message : UnderlyingStipGrpComp) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : UnderlyingStipGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UnderlyingStipGrpComp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end UnderlyingStipGrpComp

/-- Enter Tes Trade Request -/
structure EnterTesTradeRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  securityId : BitVec 64
  lastPx : BitVec 64
  transBkdTime : BitVec 64
  underlyingPx : BitVec 64
  relatedClosePrice : BitVec 64
  relatedTradeQuantity : BitVec 64
  relatedSecurityId : BitVec 64
  relatedPx : BitVec 64
  underlyingQty : BitVec 64
  marketSegmentId : BitVec 32
  underlyingSettlementDate : BitVec 32
  underlyingMaturityDate : BitVec 32
  relatedTradeId : BitVec 32
  relatedMarketSegmentId : BitVec 32
  trdType : BitVec 16
  productComplex : BitVec 8
  tradeReportType : BitVec 8
  tradePublishIndicator : BitVec 8
  partyIdSettlementLocation : BitVec 8
  hedgeType : BitVec 8
  swapClearer : BitVec 8
  tradeReportText : Alpha 20
  tradeReportId : Alpha 20
  underlyingSecurityId : Alpha 12
  underlyingSecurityDesc : Alpha 30
  underlyingCurrency : Alpha 3
  underlyingIssuer : Alpha 30
  pad4 : Alpha 4
  sideAllocGrpComp : Bounded 1 SideAllocGrpComp
  trdInstrmntLegGrpComp : Bounded 1 TrdInstrmntLegGrpComp
  instrumentEventGrpComp : Bounded 1 InstrumentEventGrpComp
  instrumentAttributeGrpComp : Bounded 1 InstrumentAttributeGrpComp
  underlyingStipGrpComp : Bounded 1 UnderlyingStipGrpComp
  deriving DecidableEq, Repr

namespace EnterTesTradeRequest

def encode (message : EnterTesTradeRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.lastPx
    ++ (encodeUIntLE 8 message.transBkdTime
    ++ (encodeUIntLE 8 message.underlyingPx
    ++ (encodeUIntLE 8 message.relatedClosePrice
    ++ (encodeUIntLE 8 message.relatedTradeQuantity
    ++ (encodeUIntLE 8 message.relatedSecurityId
    ++ (encodeUIntLE 8 message.relatedPx
    ++ (encodeUIntLE 8 message.underlyingQty
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.underlyingSettlementDate
    ++ (encodeUIntLE 4 message.underlyingMaturityDate
    ++ (encodeUIntLE 4 message.relatedTradeId
    ++ (encodeUIntLE 4 message.relatedMarketSegmentId
    ++ (encodeUIntLE 2 message.trdType
    ++ (encodeUInt 1 message.productComplex
    ++ (encodeUInt 1 message.tradeReportType
    ++ (encodeUInt 1 message.tradePublishIndicator
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.sideAllocGrpComp.val.length)
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.instrumentEventGrpComp.val.length)
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.trdInstrmntLegGrpComp.val.length)
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.instrumentAttributeGrpComp.val.length)
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.underlyingStipGrpComp.val.length)
    ++ (encodeUInt 1 message.partyIdSettlementLocation
    ++ (encodeUInt 1 message.hedgeType
    ++ (encodeUInt 1 message.swapClearer
    ++ (Alpha.encode message.tradeReportText
    ++ (Alpha.encode message.tradeReportId
    ++ (Alpha.encode message.underlyingSecurityId
    ++ (Alpha.encode message.underlyingSecurityDesc
    ++ (Alpha.encode message.underlyingCurrency
    ++ (Alpha.encode message.underlyingIssuer
    ++ (Alpha.encode message.pad4
    ++ (encodeMany SideAllocGrpComp.encode message.sideAllocGrpComp.val
    ++ (encodeMany TrdInstrmntLegGrpComp.encode message.trdInstrmntLegGrpComp.val
    ++ (encodeMany InstrumentEventGrpComp.encode message.instrumentEventGrpComp.val
    ++ (encodeMany InstrumentAttributeGrpComp.encode message.instrumentAttributeGrpComp.val
    ++ (encodeMany UnderlyingStipGrpComp.encode message.underlyingStipGrpComp.val))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (EnterTesTradeRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  let (transBkdTime, bytes) ← decodeUIntLE 8 bytes
  let (underlyingPx, bytes) ← decodeUIntLE 8 bytes
  let (relatedClosePrice, bytes) ← decodeUIntLE 8 bytes
  let (relatedTradeQuantity, bytes) ← decodeUIntLE 8 bytes
  let (relatedSecurityId, bytes) ← decodeUIntLE 8 bytes
  let (relatedPx, bytes) ← decodeUIntLE 8 bytes
  let (underlyingQty, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (underlyingSettlementDate, bytes) ← decodeUIntLE 4 bytes
  let (underlyingMaturityDate, bytes) ← decodeUIntLE 4 bytes
  let (relatedTradeId, bytes) ← decodeUIntLE 4 bytes
  let (relatedMarketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (trdType, bytes) ← decodeUIntLE 2 bytes
  let (productComplex, bytes) ← decodeUInt 1 bytes
  let (tradeReportType, bytes) ← decodeUInt 1 bytes
  let (tradePublishIndicator, bytes) ← decodeUInt 1 bytes
  let (noSideAllocs, bytes) ← decodeUInt 1 bytes
  let (noEvents, bytes) ← decodeUInt 1 bytes
  let (noLegs, bytes) ← decodeUInt 1 bytes
  let (noInstrAttrib, bytes) ← decodeUInt 1 bytes
  let (noUnderlyingStips, bytes) ← decodeUInt 1 bytes
  let (partyIdSettlementLocation, bytes) ← decodeUInt 1 bytes
  let (hedgeType, bytes) ← decodeUInt 1 bytes
  let (swapClearer, bytes) ← decodeUInt 1 bytes
  let (tradeReportText, bytes) ← Alpha.decode 20 bytes
  let (tradeReportId, bytes) ← Alpha.decode 20 bytes
  let (underlyingSecurityId, bytes) ← Alpha.decode 12 bytes
  let (underlyingSecurityDesc, bytes) ← Alpha.decode 30 bytes
  let (underlyingCurrency, bytes) ← Alpha.decode 3 bytes
  let (underlyingIssuer, bytes) ← Alpha.decode 30 bytes
  let (pad4, bytes) ← Alpha.decode 4 bytes
  let (sideAllocGrpComp_, bytes) ← decodeMany SideAllocGrpComp.decode noSideAllocs.toNat bytes
  let (trdInstrmntLegGrpComp_, bytes) ← decodeMany TrdInstrmntLegGrpComp.decode noLegs.toNat bytes
  let (instrumentEventGrpComp_, bytes) ← decodeMany InstrumentEventGrpComp.decode noEvents.toNat bytes
  let (instrumentAttributeGrpComp_, bytes) ← decodeMany InstrumentAttributeGrpComp.decode noInstrAttrib.toNat bytes
  let (underlyingStipGrpComp_, bytes) ← decodeMany UnderlyingStipGrpComp.decode noUnderlyingStips.toNat bytes
  if fits_sideAllocGrpComp : sideAllocGrpComp_.length < 256 ^ 1 then
    if fits_trdInstrmntLegGrpComp : trdInstrmntLegGrpComp_.length < 256 ^ 1 then
      if fits_instrumentEventGrpComp : instrumentEventGrpComp_.length < 256 ^ 1 then
        if fits_instrumentAttributeGrpComp : instrumentAttributeGrpComp_.length < 256 ^ 1 then
          if fits_underlyingStipGrpComp : underlyingStipGrpComp_.length < 256 ^ 1 then
            pure ({ networkMsgId, pad2, requestHeaderComp, securityId, lastPx, transBkdTime, underlyingPx, relatedClosePrice, relatedTradeQuantity, relatedSecurityId, relatedPx, underlyingQty, marketSegmentId, underlyingSettlementDate, underlyingMaturityDate, relatedTradeId, relatedMarketSegmentId, trdType, productComplex, tradeReportType, tradePublishIndicator, partyIdSettlementLocation, hedgeType, swapClearer, tradeReportText, tradeReportId, underlyingSecurityId, underlyingSecurityDesc, underlyingCurrency, underlyingIssuer, pad4, sideAllocGrpComp := ⟨sideAllocGrpComp_, fits_sideAllocGrpComp⟩, trdInstrmntLegGrpComp := ⟨trdInstrmntLegGrpComp_, fits_trdInstrmntLegGrpComp⟩, instrumentEventGrpComp := ⟨instrumentEventGrpComp_, fits_instrumentEventGrpComp⟩, instrumentAttributeGrpComp := ⟨instrumentAttributeGrpComp_, fits_instrumentAttributeGrpComp⟩, underlyingStipGrpComp := ⟨underlyingStipGrpComp_, fits_underlyingStipGrpComp⟩ }, bytes)
          else none
        else none
      else none
    else none
  else none

theorem encode_length_pos (message : EnterTesTradeRequest) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : EnterTesTradeRequest) : (encode message).length ≤ 36962 := by
  have bound_sideAllocGrpComp := message.sideAllocGrpComp.length_lt
  have bound_trdInstrmntLegGrpComp := message.trdInstrmntLegGrpComp.length_lt
  have bound_instrumentEventGrpComp := message.instrumentEventGrpComp.length_lt
  have bound_instrumentAttributeGrpComp := message.instrumentAttributeGrpComp.length_lt
  have bound_underlyingStipGrpComp := message.underlyingStipGrpComp.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const SideAllocGrpComp.encode 32 SideAllocGrpComp.encode_length, encodeMany_length_const TrdInstrmntLegGrpComp.encode 24 TrdInstrmntLegGrpComp.encode_length, encodeMany_length_const InstrumentEventGrpComp.encode 8 InstrumentEventGrpComp.encode_length, encodeMany_length_const InstrumentAttributeGrpComp.encode 40 InstrumentAttributeGrpComp.encode_length, encodeMany_length_const UnderlyingStipGrpComp.encode 40 UnderlyingStipGrpComp.encode_length]
  omega

set_option maxRecDepth 4096 in
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
  rw [List.append_assoc, decodeMany_bounded 1 SideAllocGrpComp.encode SideAllocGrpComp.decode SideAllocGrpComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeMany_bounded 1 TrdInstrmntLegGrpComp.encode TrdInstrmntLegGrpComp.decode TrdInstrmntLegGrpComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeMany_bounded 1 InstrumentEventGrpComp.encode InstrumentEventGrpComp.decode InstrumentEventGrpComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeMany_bounded 1 InstrumentAttributeGrpComp.encode InstrumentAttributeGrpComp.decode InstrumentAttributeGrpComp.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 UnderlyingStipGrpComp.encode UnderlyingStipGrpComp.decode UnderlyingStipGrpComp.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.sideAllocGrpComp.length_lt, dite_eq_left message.trdInstrmntLegGrpComp.length_lt, dite_eq_left message.instrumentEventGrpComp.length_lt, dite_eq_left message.instrumentAttributeGrpComp.length_lt, dite_eq_left message.underlyingStipGrpComp.length_lt]
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

/-- Inquire Mm Parameter Request: 26 bytes -/
structure InquireMmParameterRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  marketSegmentId : BitVec 32
  targetPartyIdSessionId : BitVec 32
  deriving DecidableEq, Repr

namespace InquireMmParameterRequest

def encode (message : InquireMmParameterRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.targetPartyIdSessionId))))

def decode (bytes : List UInt8) : Option (InquireMmParameterRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (targetPartyIdSessionId, bytes) ← decodeUIntLE 4 bytes
  pure ({ networkMsgId, pad2, requestHeaderComp, marketSegmentId, targetPartyIdSessionId }, bytes)

@[simp] theorem encode_length (message : InquireMmParameterRequest) : (encode message).length = 26 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : InquireMmParameterRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InquireMmParameterRequest) (rest : List UInt8) :
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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end InquireMmParameterRequest

/-- Inquire Margin Based Risk Limit Request: 26 bytes -/
structure InquireMarginBasedRiskLimitRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  partitionId : BitVec 16
  partyDetailExecutingUnit : Alpha 5
  pad1 : Alpha 1
  deriving DecidableEq, Repr

namespace InquireMarginBasedRiskLimitRequest

def encode (message : InquireMarginBasedRiskLimitRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 2 message.partitionId
    ++ (Alpha.encode message.partyDetailExecutingUnit
    ++ (Alpha.encode message.pad1)))))

def decode (bytes : List UInt8) : Option (InquireMarginBasedRiskLimitRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (partitionId, bytes) ← decodeUIntLE 2 bytes
  let (partyDetailExecutingUnit, bytes) ← Alpha.decode 5 bytes
  let (pad1, bytes) ← Alpha.decode 1 bytes
  pure ({ networkMsgId, pad2, requestHeaderComp, partitionId, partyDetailExecutingUnit, pad1 }, bytes)

@[simp] theorem encode_length (message : InquireMarginBasedRiskLimitRequest) : (encode message).length = 26 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : InquireMarginBasedRiskLimitRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InquireMarginBasedRiskLimitRequest) (rest : List UInt8) :
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

end InquireMarginBasedRiskLimitRequest

/-- Inquire Pre Trade Risk Limits Request: 34 bytes -/
structure InquirePreTradeRiskLimitsRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  marketSegmentId : BitVec 32
  riskLimitPlatform : BitVec 8
  partyExecutingUnit : Alpha 5
  riskLimitGroup : Alpha 3
  pad3 : Alpha 3
  deriving DecidableEq, Repr

namespace InquirePreTradeRiskLimitsRequest

def encode (message : InquirePreTradeRiskLimitsRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUInt 1 message.riskLimitPlatform
    ++ (Alpha.encode message.partyExecutingUnit
    ++ (Alpha.encode message.riskLimitGroup
    ++ (Alpha.encode message.pad3)))))))

def decode (bytes : List UInt8) : Option (InquirePreTradeRiskLimitsRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (riskLimitPlatform, bytes) ← decodeUInt 1 bytes
  let (partyExecutingUnit, bytes) ← Alpha.decode 5 bytes
  let (riskLimitGroup, bytes) ← Alpha.decode 3 bytes
  let (pad3, bytes) ← Alpha.decode 3 bytes
  pure ({ networkMsgId, pad2, requestHeaderComp, marketSegmentId, riskLimitPlatform, partyExecutingUnit, riskLimitGroup, pad3 }, bytes)

@[simp] theorem encode_length (message : InquirePreTradeRiskLimitsRequest) : (encode message).length = 34 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : InquirePreTradeRiskLimitsRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InquirePreTradeRiskLimitsRequest) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end InquirePreTradeRiskLimitsRequest

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

/-- Logon Request Encrypted: 930 bytes -/
structure LogonRequestEncrypted where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  heartBtInt : BitVec 32
  partyIdSessionId : BitVec 32
  defaultCstmApplVerId : Alpha 30
  encryptedPassword : Alpha 684
  applUsageOrders : ApplUsageOrders
  applUsageQuotes : ApplUsageQuotes
  orderRoutingIndicator : OrderRoutingIndicator
  fixEngineName : Alpha 30
  fixEngineVersion : Alpha 30
  fixEngineVendor : Alpha 30
  applicationSystemName : Alpha 30
  applicationSystemVersion : Alpha 30
  applicationSystemVendor : Alpha 30
  pad7 : Alpha 7
  deriving DecidableEq, Repr

namespace LogonRequestEncrypted

def encode (message : LogonRequestEncrypted) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 4 message.heartBtInt
    ++ (encodeUIntLE 4 message.partyIdSessionId
    ++ (Alpha.encode message.defaultCstmApplVerId
    ++ (Alpha.encode message.encryptedPassword
    ++ (ApplUsageOrders.encode message.applUsageOrders
    ++ (ApplUsageQuotes.encode message.applUsageQuotes
    ++ (OrderRoutingIndicator.encode message.orderRoutingIndicator
    ++ (Alpha.encode message.fixEngineName
    ++ (Alpha.encode message.fixEngineVersion
    ++ (Alpha.encode message.fixEngineVendor
    ++ (Alpha.encode message.applicationSystemName
    ++ (Alpha.encode message.applicationSystemVersion
    ++ (Alpha.encode message.applicationSystemVendor
    ++ (Alpha.encode message.pad7))))))))))))))))

def decode (bytes : List UInt8) : Option (LogonRequestEncrypted × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (heartBtInt, bytes) ← decodeUIntLE 4 bytes
  let (partyIdSessionId, bytes) ← decodeUIntLE 4 bytes
  let (defaultCstmApplVerId, bytes) ← Alpha.decode 30 bytes
  let (encryptedPassword, bytes) ← Alpha.decode 684 bytes
  let (applUsageOrders, bytes) ← ApplUsageOrders.decode bytes
  let (applUsageQuotes, bytes) ← ApplUsageQuotes.decode bytes
  let (orderRoutingIndicator, bytes) ← OrderRoutingIndicator.decode bytes
  let (fixEngineName, bytes) ← Alpha.decode 30 bytes
  let (fixEngineVersion, bytes) ← Alpha.decode 30 bytes
  let (fixEngineVendor, bytes) ← Alpha.decode 30 bytes
  let (applicationSystemName, bytes) ← Alpha.decode 30 bytes
  let (applicationSystemVersion, bytes) ← Alpha.decode 30 bytes
  let (applicationSystemVendor, bytes) ← Alpha.decode 30 bytes
  let (pad7, bytes) ← Alpha.decode 7 bytes
  pure ({ networkMsgId, pad2, requestHeaderComp, heartBtInt, partyIdSessionId, defaultCstmApplVerId, encryptedPassword, applUsageOrders, applUsageQuotes, orderRoutingIndicator, fixEngineName, fixEngineVersion, fixEngineVendor, applicationSystemName, applicationSystemVersion, applicationSystemVendor, pad7 }, bytes)

@[simp] theorem encode_length (message : LogonRequestEncrypted) : (encode message).length = 930 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length, ApplUsageOrders.encode_length, ApplUsageQuotes.encode_length, OrderRoutingIndicator.encode_length]

theorem encode_length_pos (message : LogonRequestEncrypted) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LogonRequestEncrypted) (rest : List UInt8) :
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

end LogonRequestEncrypted

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

/-- Mm Parameter Definition Request: 66 bytes -/
structure MmParameterDefinitionRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  exposureDuration : BitVec 64
  cumQty : BitVec 64
  delta : BitVec 64
  vega : BitVec 64
  marketSegmentId : BitVec 32
  targetPartyIdSessionId : BitVec 32
  pctCount : BitVec 32
  pad4 : Alpha 4
  deriving DecidableEq, Repr

namespace MmParameterDefinitionRequest

def encode (message : MmParameterDefinitionRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 8 message.exposureDuration
    ++ (encodeUIntLE 8 message.cumQty
    ++ (encodeUIntLE 8 message.delta
    ++ (encodeUIntLE 8 message.vega
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.targetPartyIdSessionId
    ++ (encodeUIntLE 4 message.pctCount
    ++ (Alpha.encode message.pad4))))))))))

def decode (bytes : List UInt8) : Option (MmParameterDefinitionRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (exposureDuration, bytes) ← decodeUIntLE 8 bytes
  let (cumQty, bytes) ← decodeUIntLE 8 bytes
  let (delta, bytes) ← decodeUIntLE 8 bytes
  let (vega, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (targetPartyIdSessionId, bytes) ← decodeUIntLE 4 bytes
  let (pctCount, bytes) ← decodeUIntLE 4 bytes
  let (pad4, bytes) ← Alpha.decode 4 bytes
  pure ({ networkMsgId, pad2, requestHeaderComp, exposureDuration, cumQty, delta, vega, marketSegmentId, targetPartyIdSessionId, pctCount, pad4 }, bytes)

@[simp] theorem encode_length (message : MmParameterDefinitionRequest) : (encode message).length = 66 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : MmParameterDefinitionRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MmParameterDefinitionRequest) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end MmParameterDefinitionRequest

/-- Order Entry Grp Comp: 40 bytes -/
structure OrderEntryGrpComp where
  price : BitVec 64
  orderQty : BitVec 64
  marketSegmentId : BitVec 32
  pad4 : Alpha 4
  securityId : BitVec 64
  side : BitVec 8
  productComplex : BitVec 8
  pad6 : Alpha 6
  deriving DecidableEq, Repr

namespace OrderEntryGrpComp

def encode (message : OrderEntryGrpComp) : List UInt8 :=
  encodeUIntLE 8 message.price
    ++ (encodeUIntLE 8 message.orderQty
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (Alpha.encode message.pad4
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUInt 1 message.side
    ++ (encodeUInt 1 message.productComplex
    ++ (Alpha.encode message.pad6)))))))

def decode (bytes : List UInt8) : Option (OrderEntryGrpComp × List UInt8) := do
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (orderQty, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (pad4, bytes) ← Alpha.decode 4 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (productComplex, bytes) ← decodeUInt 1 bytes
  let (pad6, bytes) ← Alpha.decode 6 bytes
  pure ({ price, orderQty, marketSegmentId, pad4, securityId, side, productComplex, pad6 }, bytes)

@[simp] theorem encode_length (message : OrderEntryGrpComp) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : OrderEntryGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderEntryGrpComp) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderEntryGrpComp

/-- Mass Order -/
structure MassOrder where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  massOrderRequestId : BitVec 64
  partyIdClientId : BitVec 64
  partyIdInvestmentDecisionMaker : BitVec 64
  executingTrader : BitVec 64
  partyIdTakeUpTradingFirm : Alpha 5
  partyIdOrderOriginationFirm : Alpha 7
  partyIdBeneficiary : Alpha 9
  priceValidityCheckType : BitVec 8
  valueCheckTypeValue : BitVec 8
  orderAttributeLiquidityProvision : BitVec 8
  orderAttributeRiskReduction : BitVec 8
  tradingSessionSubId : BitVec 8
  tradingCapacity : BitVec 8
  orderOrigination : BitVec 8
  partyIdInvestmentDecisionMakerQualifier : BitVec 8
  executingTraderQualifier : BitVec 8
  account : Alpha 2
  partyIdPositionAccount : Alpha 32
  positionEffect : PositionEffect
  partyIdLocationId : Alpha 2
  custOrderHandlingInst : CustOrderHandlingInst
  complianceText : Alpha 20
  freeText1 : Alpha 12
  freeText2 : Alpha 12
  freeText3 : Alpha 12
  partyEndClientIdentification : Alpha 20
  pad7 : Alpha 7
  orderEntryGrpComp : Bounded 1 OrderEntryGrpComp
  deriving DecidableEq, Repr

namespace MassOrder

def encode (message : MassOrder) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 8 message.massOrderRequestId
    ++ (encodeUIntLE 8 message.partyIdClientId
    ++ (encodeUIntLE 8 message.partyIdInvestmentDecisionMaker
    ++ (encodeUIntLE 8 message.executingTrader
    ++ (Alpha.encode message.partyIdTakeUpTradingFirm
    ++ (Alpha.encode message.partyIdOrderOriginationFirm
    ++ (Alpha.encode message.partyIdBeneficiary
    ++ (encodeUInt 1 message.priceValidityCheckType
    ++ (encodeUInt 1 message.valueCheckTypeValue
    ++ (encodeUInt 1 message.orderAttributeLiquidityProvision
    ++ (encodeUInt 1 message.orderAttributeRiskReduction
    ++ (encodeUInt 1 message.tradingSessionSubId
    ++ (encodeUInt 1 message.tradingCapacity
    ++ (encodeUInt 1 message.orderOrigination
    ++ (encodeUInt 1 message.partyIdInvestmentDecisionMakerQualifier
    ++ (encodeUInt 1 message.executingTraderQualifier
    ++ (Alpha.encode message.account
    ++ (Alpha.encode message.partyIdPositionAccount
    ++ (PositionEffect.encode message.positionEffect
    ++ (Alpha.encode message.partyIdLocationId
    ++ (CustOrderHandlingInst.encode message.custOrderHandlingInst
    ++ (Alpha.encode message.complianceText
    ++ (Alpha.encode message.freeText1
    ++ (Alpha.encode message.freeText2
    ++ (Alpha.encode message.freeText3
    ++ (Alpha.encode message.partyEndClientIdentification
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.orderEntryGrpComp.val.length)
    ++ (Alpha.encode message.pad7
    ++ (encodeMany OrderEntryGrpComp.encode message.orderEntryGrpComp.val)))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (MassOrder × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (massOrderRequestId, bytes) ← decodeUIntLE 8 bytes
  let (partyIdClientId, bytes) ← decodeUIntLE 8 bytes
  let (partyIdInvestmentDecisionMaker, bytes) ← decodeUIntLE 8 bytes
  let (executingTrader, bytes) ← decodeUIntLE 8 bytes
  let (partyIdTakeUpTradingFirm, bytes) ← Alpha.decode 5 bytes
  let (partyIdOrderOriginationFirm, bytes) ← Alpha.decode 7 bytes
  let (partyIdBeneficiary, bytes) ← Alpha.decode 9 bytes
  let (priceValidityCheckType, bytes) ← decodeUInt 1 bytes
  let (valueCheckTypeValue, bytes) ← decodeUInt 1 bytes
  let (orderAttributeLiquidityProvision, bytes) ← decodeUInt 1 bytes
  let (orderAttributeRiskReduction, bytes) ← decodeUInt 1 bytes
  let (tradingSessionSubId, bytes) ← decodeUInt 1 bytes
  let (tradingCapacity, bytes) ← decodeUInt 1 bytes
  let (orderOrigination, bytes) ← decodeUInt 1 bytes
  let (partyIdInvestmentDecisionMakerQualifier, bytes) ← decodeUInt 1 bytes
  let (executingTraderQualifier, bytes) ← decodeUInt 1 bytes
  let (account, bytes) ← Alpha.decode 2 bytes
  let (partyIdPositionAccount, bytes) ← Alpha.decode 32 bytes
  let (positionEffect, bytes) ← PositionEffect.decode bytes
  let (partyIdLocationId, bytes) ← Alpha.decode 2 bytes
  let (custOrderHandlingInst, bytes) ← CustOrderHandlingInst.decode bytes
  let (complianceText, bytes) ← Alpha.decode 20 bytes
  let (freeText1, bytes) ← Alpha.decode 12 bytes
  let (freeText2, bytes) ← Alpha.decode 12 bytes
  let (freeText3, bytes) ← Alpha.decode 12 bytes
  let (partyEndClientIdentification, bytes) ← Alpha.decode 20 bytes
  let (noOrderEntries, bytes) ← decodeUInt 1 bytes
  let (pad7, bytes) ← Alpha.decode 7 bytes
  let (orderEntryGrpComp_, bytes) ← decodeMany OrderEntryGrpComp.decode noOrderEntries.toNat bytes
  if fits_orderEntryGrpComp : orderEntryGrpComp_.length < 256 ^ 1 then
    pure ({ networkMsgId, pad2, requestHeaderComp, massOrderRequestId, partyIdClientId, partyIdInvestmentDecisionMaker, executingTrader, partyIdTakeUpTradingFirm, partyIdOrderOriginationFirm, partyIdBeneficiary, priceValidityCheckType, valueCheckTypeValue, orderAttributeLiquidityProvision, orderAttributeRiskReduction, tradingSessionSubId, tradingCapacity, orderOrigination, partyIdInvestmentDecisionMakerQualifier, executingTraderQualifier, account, partyIdPositionAccount, positionEffect, partyIdLocationId, custOrderHandlingInst, complianceText, freeText1, freeText2, freeText3, partyEndClientIdentification, pad7, orderEntryGrpComp := ⟨orderEntryGrpComp_, fits_orderEntryGrpComp⟩ }, bytes)
  else none

theorem encode_length_pos (message : MassOrder) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MassOrder) : (encode message).length ≤ 10402 := by
  have bound_orderEntryGrpComp := message.orderEntryGrpComp.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length, PositionEffect.encode_length, CustOrderHandlingInst.encode_length, encodeMany_length_const OrderEntryGrpComp.encode 40 OrderEntryGrpComp.encode_length]
  omega

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : MassOrder) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, PositionEffect.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CustOrderHandlingInst.decode_encode, some_bind]
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
  rw [decodeMany_bounded 1 OrderEntryGrpComp.encode OrderEntryGrpComp.decode OrderEntryGrpComp.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.orderEntryGrpComp.length_lt]
  rfl

end MassOrder

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
  selfMatchPreventionInstruction : BitVec 8
  priceValidityCheckType : BitVec 8
  valueCheckTypeValue : BitVec 8
  quoteSizeType : BitVec 8
  quoteType : BitVec 8
  orderAttributeLiquidityProvision : BitVec 8
  partyIdInvestmentDecisionMakerQualifier : BitVec 8
  executingTraderQualifier : BitVec 8
  pad5 : Alpha 5
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
    ++ (encodeUInt 1 message.selfMatchPreventionInstruction
    ++ (encodeUInt 1 message.priceValidityCheckType
    ++ (encodeUInt 1 message.valueCheckTypeValue
    ++ (encodeUInt 1 message.quoteSizeType
    ++ (encodeUInt 1 message.quoteType
    ++ (encodeUInt 1 message.orderAttributeLiquidityProvision
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.quoteEntryGrpComp.val.length)
    ++ (encodeUInt 1 message.partyIdInvestmentDecisionMakerQualifier
    ++ (encodeUInt 1 message.executingTraderQualifier
    ++ (Alpha.encode message.pad5
    ++ (encodeMany QuoteEntryGrpComp.encode message.quoteEntryGrpComp.val)))))))))))))))))))

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
  let (selfMatchPreventionInstruction, bytes) ← decodeUInt 1 bytes
  let (priceValidityCheckType, bytes) ← decodeUInt 1 bytes
  let (valueCheckTypeValue, bytes) ← decodeUInt 1 bytes
  let (quoteSizeType, bytes) ← decodeUInt 1 bytes
  let (quoteType, bytes) ← decodeUInt 1 bytes
  let (orderAttributeLiquidityProvision, bytes) ← decodeUInt 1 bytes
  let (noQuoteEntries, bytes) ← decodeUInt 1 bytes
  let (partyIdInvestmentDecisionMakerQualifier, bytes) ← decodeUInt 1 bytes
  let (executingTraderQualifier, bytes) ← decodeUInt 1 bytes
  let (pad5, bytes) ← Alpha.decode 5 bytes
  let (quoteEntryGrpComp_, bytes) ← decodeMany QuoteEntryGrpComp.decode noQuoteEntries.toNat bytes
  if fits_quoteEntryGrpComp : quoteEntryGrpComp_.length < 256 ^ 1 then
    pure ({ networkMsgId, pad2, requestHeaderComp, quoteId, partyIdInvestmentDecisionMaker, executingTrader, marketSegmentId, matchInstCrossId, enrichmentRuleId, selfMatchPreventionInstruction, priceValidityCheckType, valueCheckTypeValue, quoteSizeType, quoteType, orderAttributeLiquidityProvision, partyIdInvestmentDecisionMakerQualifier, executingTraderQualifier, pad5, quoteEntryGrpComp := ⟨quoteEntryGrpComp_, fits_quoteEntryGrpComp⟩ }, bytes)
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 QuoteEntryGrpComp.encode QuoteEntryGrpComp.decode QuoteEntryGrpComp.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.quoteEntryGrpComp.length_lt]
  rfl

end MassQuoteRequest

/-- Modify Basket Trade Request -/
structure ModifyBasketTradeRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  basketTrdMatchId : BitVec 64
  basketExecId : BitVec 32
  marketSegmentId : BitVec 32
  maturityMonthYear : BitVec 32
  basketProfileId : BitVec 32
  trdType : BitVec 16
  tradeReportType : BitVec 8
  basketTradeReportText : Alpha 20
  tradeReportId : Alpha 20
  pad1 : Alpha 1
  basketRootPartyGrpComp : Bounded 1 BasketRootPartyGrpComp
  instrmtMatchSideGrpComp : Bounded 1 InstrmtMatchSideGrpComp
  basketSideAllocGrpComp : Bounded 2 BasketSideAllocGrpComp
  deriving DecidableEq, Repr

namespace ModifyBasketTradeRequest

def encode (message : ModifyBasketTradeRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 8 message.basketTrdMatchId
    ++ (encodeUIntLE 4 message.basketExecId
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.maturityMonthYear
    ++ (encodeUIntLE 4 message.basketProfileId
    ++ (encodeUIntLE 2 message.trdType
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.basketSideAllocGrpComp.val.length)
    ++ (encodeUInt 1 message.tradeReportType
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.basketRootPartyGrpComp.val.length)
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.instrmtMatchSideGrpComp.val.length)
    ++ (Alpha.encode message.basketTradeReportText
    ++ (Alpha.encode message.tradeReportId
    ++ (Alpha.encode message.pad1
    ++ (encodeMany BasketRootPartyGrpComp.encode message.basketRootPartyGrpComp.val
    ++ (encodeMany InstrmtMatchSideGrpComp.encode message.instrmtMatchSideGrpComp.val
    ++ (encodeMany BasketSideAllocGrpComp.encode message.basketSideAllocGrpComp.val))))))))))))))))))

def decode (bytes : List UInt8) : Option (ModifyBasketTradeRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (basketTrdMatchId, bytes) ← decodeUIntLE 8 bytes
  let (basketExecId, bytes) ← decodeUIntLE 4 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (maturityMonthYear, bytes) ← decodeUIntLE 4 bytes
  let (basketProfileId, bytes) ← decodeUIntLE 4 bytes
  let (trdType, bytes) ← decodeUIntLE 2 bytes
  let (noBasketSideAlloc, bytes) ← decodeUIntLE 2 bytes
  let (tradeReportType, bytes) ← decodeUInt 1 bytes
  let (noBasketRootPartyGrps, bytes) ← decodeUInt 1 bytes
  let (noInstrmtMatchSides, bytes) ← decodeUInt 1 bytes
  let (basketTradeReportText, bytes) ← Alpha.decode 20 bytes
  let (tradeReportId, bytes) ← Alpha.decode 20 bytes
  let (pad1, bytes) ← Alpha.decode 1 bytes
  let (basketRootPartyGrpComp_, bytes) ← decodeMany BasketRootPartyGrpComp.decode noBasketRootPartyGrps.toNat bytes
  let (instrmtMatchSideGrpComp_, bytes) ← decodeMany InstrmtMatchSideGrpComp.decode noInstrmtMatchSides.toNat bytes
  let (basketSideAllocGrpComp_, bytes) ← decodeMany BasketSideAllocGrpComp.decode noBasketSideAlloc.toNat bytes
  if fits_basketRootPartyGrpComp : basketRootPartyGrpComp_.length < 256 ^ 1 then
    if fits_instrmtMatchSideGrpComp : instrmtMatchSideGrpComp_.length < 256 ^ 1 then
      if fits_basketSideAllocGrpComp : basketSideAllocGrpComp_.length < 256 ^ 2 then
        pure ({ networkMsgId, pad2, requestHeaderComp, basketTrdMatchId, basketExecId, marketSegmentId, maturityMonthYear, basketProfileId, trdType, tradeReportType, basketTradeReportText, tradeReportId, pad1, basketRootPartyGrpComp := ⟨basketRootPartyGrpComp_, fits_basketRootPartyGrpComp⟩, instrmtMatchSideGrpComp := ⟨instrmtMatchSideGrpComp_, fits_instrmtMatchSideGrpComp⟩, basketSideAllocGrpComp := ⟨basketSideAllocGrpComp_, fits_basketSideAllocGrpComp⟩ }, bytes)
      else none
    else none
  else none

theorem encode_length_pos (message : ModifyBasketTradeRequest) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ModifyBasketTradeRequest) : (encode message).length ≤ 2127810 := by
  have bound_basketRootPartyGrpComp := message.basketRootPartyGrpComp.length_lt
  have bound_instrmtMatchSideGrpComp := message.instrmtMatchSideGrpComp.length_lt
  have bound_basketSideAllocGrpComp := message.basketSideAllocGrpComp.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const BasketRootPartyGrpComp.encode 40 BasketRootPartyGrpComp.encode_length, encodeMany_length_const InstrmtMatchSideGrpComp.encode 80 InstrmtMatchSideGrpComp.encode_length, encodeMany_length_const BasketSideAllocGrpComp.encode 32 BasketSideAllocGrpComp.encode_length]
  omega

@[simp] theorem decode_encode (message : ModifyBasketTradeRequest) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeMany_bounded 1 BasketRootPartyGrpComp.encode BasketRootPartyGrpComp.decode BasketRootPartyGrpComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeMany_bounded 1 InstrmtMatchSideGrpComp.encode InstrmtMatchSideGrpComp.decode InstrmtMatchSideGrpComp.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 BasketSideAllocGrpComp.encode BasketSideAllocGrpComp.decode BasketSideAllocGrpComp.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.basketRootPartyGrpComp.length_lt, dite_eq_left message.instrmtMatchSideGrpComp.length_lt, dite_eq_left message.basketSideAllocGrpComp.length_lt]
  rfl

end ModifyBasketTradeRequest

/-- Leg Ord Grp Comp: 8 bytes -/
structure LegOrdGrpComp where
  legAccount : Alpha 2
  legPositionEffect : LegPositionEffect
  pad5 : Alpha 5
  deriving DecidableEq, Repr

namespace LegOrdGrpComp

def encode (message : LegOrdGrpComp) : List UInt8 :=
  Alpha.encode message.legAccount
    ++ (LegPositionEffect.encode message.legPositionEffect
    ++ (Alpha.encode message.pad5))

def decode (bytes : List UInt8) : Option (LegOrdGrpComp × List UInt8) := do
  let (legAccount, bytes) ← Alpha.decode 2 bytes
  let (legPositionEffect, bytes) ← LegPositionEffect.decode bytes
  let (pad5, bytes) ← Alpha.decode 5 bytes
  pure ({ legAccount, legPositionEffect, pad5 }, bytes)

@[simp] theorem encode_length (message : LegOrdGrpComp) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, LegPositionEffect.encode_length]

theorem encode_length_pos (message : LegOrdGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LegOrdGrpComp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, LegPositionEffect.decode_encode, some_bind]
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
  orderQty : BitVec 64
  partyIdClientId : BitVec 64
  partyIdInvestmentDecisionMaker : BitVec 64
  executingTrader : BitVec 64
  marketSegmentId : BitVec 32
  expireDate : BitVec 32
  matchInstCrossId : BitVec 32
  targetPartyIdSessionId : BitVec 32
  partyIdTakeUpTradingFirm : Alpha 5
  partyIdOrderOriginationFirm : Alpha 7
  partyIdBeneficiary : Alpha 9
  applSeqIndicator : BitVec 8
  selfMatchPreventionInstruction : BitVec 8
  productComplex : BitVec 8
  side : BitVec 8
  ordType : BitVec 8
  priceValidityCheckType : BitVec 8
  valueCheckTypeValue : BitVec 8
  orderAttributeLiquidityProvision : BitVec 8
  execInst : BitVec 8
  timeInForce : BitVec 8
  tradingCapacity : BitVec 8
  ownershipIndicator : BitVec 8
  orderOrigination : BitVec 8
  partyIdInvestmentDecisionMakerQualifier : BitVec 8
  executingTraderQualifier : BitVec 8
  partyIdLocationId : Alpha 2
  custOrderHandlingInst : CustOrderHandlingInst
  complianceText : Alpha 20
  partyIdPositionAccount : Alpha 32
  freeText1 : Alpha 12
  freeText2 : Alpha 12
  freeText3 : Alpha 12
  fixClOrdId : Alpha 20
  partyEndClientIdentification : Alpha 20
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
    ++ (encodeUIntLE 8 message.orderQty
    ++ (encodeUIntLE 8 message.partyIdClientId
    ++ (encodeUIntLE 8 message.partyIdInvestmentDecisionMaker
    ++ (encodeUIntLE 8 message.executingTrader
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.expireDate
    ++ (encodeUIntLE 4 message.matchInstCrossId
    ++ (encodeUIntLE 4 message.targetPartyIdSessionId
    ++ (Alpha.encode message.partyIdTakeUpTradingFirm
    ++ (Alpha.encode message.partyIdOrderOriginationFirm
    ++ (Alpha.encode message.partyIdBeneficiary
    ++ (encodeUInt 1 message.applSeqIndicator
    ++ (encodeUInt 1 message.selfMatchPreventionInstruction
    ++ (encodeUInt 1 message.productComplex
    ++ (encodeUInt 1 message.side
    ++ (encodeUInt 1 message.ordType
    ++ (encodeUInt 1 message.priceValidityCheckType
    ++ (encodeUInt 1 message.valueCheckTypeValue
    ++ (encodeUInt 1 message.orderAttributeLiquidityProvision
    ++ (encodeUInt 1 message.execInst
    ++ (encodeUInt 1 message.timeInForce
    ++ (encodeUInt 1 message.tradingCapacity
    ++ (encodeUInt 1 message.ownershipIndicator
    ++ (encodeUInt 1 message.orderOrigination
    ++ (encodeUInt 1 message.partyIdInvestmentDecisionMakerQualifier
    ++ (encodeUInt 1 message.executingTraderQualifier
    ++ (Alpha.encode message.partyIdLocationId
    ++ (CustOrderHandlingInst.encode message.custOrderHandlingInst
    ++ (Alpha.encode message.complianceText
    ++ (Alpha.encode message.partyIdPositionAccount
    ++ (Alpha.encode message.freeText1
    ++ (Alpha.encode message.freeText2
    ++ (Alpha.encode message.freeText3
    ++ (Alpha.encode message.fixClOrdId
    ++ (Alpha.encode message.partyEndClientIdentification
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.legOrdGrpComp.val.length)
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
  let (orderQty, bytes) ← decodeUIntLE 8 bytes
  let (partyIdClientId, bytes) ← decodeUIntLE 8 bytes
  let (partyIdInvestmentDecisionMaker, bytes) ← decodeUIntLE 8 bytes
  let (executingTrader, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (expireDate, bytes) ← decodeUIntLE 4 bytes
  let (matchInstCrossId, bytes) ← decodeUIntLE 4 bytes
  let (targetPartyIdSessionId, bytes) ← decodeUIntLE 4 bytes
  let (partyIdTakeUpTradingFirm, bytes) ← Alpha.decode 5 bytes
  let (partyIdOrderOriginationFirm, bytes) ← Alpha.decode 7 bytes
  let (partyIdBeneficiary, bytes) ← Alpha.decode 9 bytes
  let (applSeqIndicator, bytes) ← decodeUInt 1 bytes
  let (selfMatchPreventionInstruction, bytes) ← decodeUInt 1 bytes
  let (productComplex, bytes) ← decodeUInt 1 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (ordType, bytes) ← decodeUInt 1 bytes
  let (priceValidityCheckType, bytes) ← decodeUInt 1 bytes
  let (valueCheckTypeValue, bytes) ← decodeUInt 1 bytes
  let (orderAttributeLiquidityProvision, bytes) ← decodeUInt 1 bytes
  let (execInst, bytes) ← decodeUInt 1 bytes
  let (timeInForce, bytes) ← decodeUInt 1 bytes
  let (tradingCapacity, bytes) ← decodeUInt 1 bytes
  let (ownershipIndicator, bytes) ← decodeUInt 1 bytes
  let (orderOrigination, bytes) ← decodeUInt 1 bytes
  let (partyIdInvestmentDecisionMakerQualifier, bytes) ← decodeUInt 1 bytes
  let (executingTraderQualifier, bytes) ← decodeUInt 1 bytes
  let (partyIdLocationId, bytes) ← Alpha.decode 2 bytes
  let (custOrderHandlingInst, bytes) ← CustOrderHandlingInst.decode bytes
  let (complianceText, bytes) ← Alpha.decode 20 bytes
  let (partyIdPositionAccount, bytes) ← Alpha.decode 32 bytes
  let (freeText1, bytes) ← Alpha.decode 12 bytes
  let (freeText2, bytes) ← Alpha.decode 12 bytes
  let (freeText3, bytes) ← Alpha.decode 12 bytes
  let (fixClOrdId, bytes) ← Alpha.decode 20 bytes
  let (partyEndClientIdentification, bytes) ← Alpha.decode 20 bytes
  let (noLegOnbooks, bytes) ← decodeUInt 1 bytes
  let (legOrdGrpComp_, bytes) ← decodeMany LegOrdGrpComp.decode noLegOnbooks.toNat bytes
  if fits_legOrdGrpComp : legOrdGrpComp_.length < 256 ^ 1 then
    pure ({ networkMsgId, pad2, requestHeaderComp, orderId, clOrdId, origClOrdId, securityId, price, orderQty, partyIdClientId, partyIdInvestmentDecisionMaker, executingTrader, marketSegmentId, expireDate, matchInstCrossId, targetPartyIdSessionId, partyIdTakeUpTradingFirm, partyIdOrderOriginationFirm, partyIdBeneficiary, applSeqIndicator, selfMatchPreventionInstruction, productComplex, side, ordType, priceValidityCheckType, valueCheckTypeValue, orderAttributeLiquidityProvision, execInst, timeInForce, tradingCapacity, ownershipIndicator, orderOrigination, partyIdInvestmentDecisionMakerQualifier, executingTraderQualifier, partyIdLocationId, custOrderHandlingInst, complianceText, partyIdPositionAccount, freeText1, freeText2, freeText3, fixClOrdId, partyEndClientIdentification, legOrdGrpComp := ⟨legOrdGrpComp_, fits_legOrdGrpComp⟩ }, bytes)
  else none

theorem encode_length_pos (message : ModifyOrderComplexRequest) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ModifyOrderComplexRequest) : (encode message).length ≤ 2314 := by
  have bound_legOrdGrpComp := message.legOrdGrpComp.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length, CustOrderHandlingInst.encode_length, encodeMany_length_const LegOrdGrpComp.encode 8 LegOrdGrpComp.encode_length]
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
  rw [List.append_assoc, CustOrderHandlingInst.decode_encode, some_bind]
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
  rw [decodeMany_bounded 1 LegOrdGrpComp.encode LegOrdGrpComp.decode LegOrdGrpComp.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.legOrdGrpComp.length_lt]
  rfl

end ModifyOrderComplexRequest

/-- Modify Order Complex Short Request: 130 bytes -/
structure ModifyOrderComplexShortRequest where
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
  marketSegmentId : BitVec 32
  matchInstCrossId : BitVec 32
  enrichmentRuleId : BitVec 16
  applSeqIndicator : BitVec 8
  selfMatchPreventionInstruction : BitVec 8
  productComplex : BitVec 8
  side : BitVec 8
  priceValidityCheckType : BitVec 8
  valueCheckTypeValue : BitVec 8
  orderAttributeLiquidityProvision : BitVec 8
  execInst : BitVec 8
  timeInForce : BitVec 8
  tradingCapacity : BitVec 8
  orderOrigination : BitVec 8
  partyIdInvestmentDecisionMakerQualifier : BitVec 8
  executingTraderQualifier : BitVec 8
  complianceText : Alpha 20
  pad5 : Alpha 5
  deriving DecidableEq, Repr

namespace ModifyOrderComplexShortRequest

def encode (message : ModifyOrderComplexShortRequest) : List UInt8 :=
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
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.matchInstCrossId
    ++ (encodeUIntLE 2 message.enrichmentRuleId
    ++ (encodeUInt 1 message.applSeqIndicator
    ++ (encodeUInt 1 message.selfMatchPreventionInstruction
    ++ (encodeUInt 1 message.productComplex
    ++ (encodeUInt 1 message.side
    ++ (encodeUInt 1 message.priceValidityCheckType
    ++ (encodeUInt 1 message.valueCheckTypeValue
    ++ (encodeUInt 1 message.orderAttributeLiquidityProvision
    ++ (encodeUInt 1 message.execInst
    ++ (encodeUInt 1 message.timeInForce
    ++ (encodeUInt 1 message.tradingCapacity
    ++ (encodeUInt 1 message.orderOrigination
    ++ (encodeUInt 1 message.partyIdInvestmentDecisionMakerQualifier
    ++ (encodeUInt 1 message.executingTraderQualifier
    ++ (Alpha.encode message.complianceText
    ++ (Alpha.encode message.pad5))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (ModifyOrderComplexShortRequest × List UInt8) := do
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
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (matchInstCrossId, bytes) ← decodeUIntLE 4 bytes
  let (enrichmentRuleId, bytes) ← decodeUIntLE 2 bytes
  let (applSeqIndicator, bytes) ← decodeUInt 1 bytes
  let (selfMatchPreventionInstruction, bytes) ← decodeUInt 1 bytes
  let (productComplex, bytes) ← decodeUInt 1 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (priceValidityCheckType, bytes) ← decodeUInt 1 bytes
  let (valueCheckTypeValue, bytes) ← decodeUInt 1 bytes
  let (orderAttributeLiquidityProvision, bytes) ← decodeUInt 1 bytes
  let (execInst, bytes) ← decodeUInt 1 bytes
  let (timeInForce, bytes) ← decodeUInt 1 bytes
  let (tradingCapacity, bytes) ← decodeUInt 1 bytes
  let (orderOrigination, bytes) ← decodeUInt 1 bytes
  let (partyIdInvestmentDecisionMakerQualifier, bytes) ← decodeUInt 1 bytes
  let (executingTraderQualifier, bytes) ← decodeUInt 1 bytes
  let (complianceText, bytes) ← Alpha.decode 20 bytes
  let (pad5, bytes) ← Alpha.decode 5 bytes
  pure ({ networkMsgId, pad2, requestHeaderComp, clOrdId, origClOrdId, securityId, price, orderQty, partyIdClientId, partyIdInvestmentDecisionMaker, executingTrader, marketSegmentId, matchInstCrossId, enrichmentRuleId, applSeqIndicator, selfMatchPreventionInstruction, productComplex, side, priceValidityCheckType, valueCheckTypeValue, orderAttributeLiquidityProvision, execInst, timeInForce, tradingCapacity, orderOrigination, partyIdInvestmentDecisionMakerQualifier, executingTraderQualifier, complianceText, pad5 }, bytes)

@[simp] theorem encode_length (message : ModifyOrderComplexShortRequest) : (encode message).length = 130 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : ModifyOrderComplexShortRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : ModifyOrderComplexShortRequest) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end ModifyOrderComplexShortRequest

/-- Modify Order Request -/
structure ModifyOrderRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  orderId : BitVec 64
  clOrdId : BitVec 64
  origClOrdId : BitVec 64
  stopPx : BitVec 64
  partyIdClientId : BitVec 64
  executingTrader : BitVec 64
  matchInstCrossId : BitVec 32
  expireDate : BitVec 32
  targetPartyIdSessionId : BitVec 32
  tradingSessionSubId : BitVec 8
  ownershipIndicator : BitVec 8
  applSeqIndicator : BitVec 8
  ordType : BitVec 8
  priceValidityCheckType : BitVec 8
  valueCheckTypeValue : BitVec 8
  orderOrigination : BitVec 8
  partyIdTakeUpTradingFirm : Alpha 5
  partyIdOrderOriginationFirm : Alpha 7
  partyIdBeneficiary : Alpha 9
  account : Alpha 2
  partyIdPositionAccount : Alpha 32
  positionEffect : PositionEffect
  partyIdLocationId : Alpha 2
  custOrderHandlingInst : CustOrderHandlingInst
  complianceText : Alpha 20
  freeText1 : Alpha 12
  freeText2 : Alpha 12
  freeText3 : Alpha 12
  fixClOrdId : Alpha 20
  partyEndClientIdentification : Alpha 20
  executingTraderQualifier : BitVec 8
  partyIdInvestmentDecisionMakerQualifier : BitVec 8
  partyIdInvestmentDecisionMaker : BitVec 64
  orderAttributeLiquidityProvision : BitVec 8
  tradingCapacity : BitVec 8
  productComplex : BitVec 8
  selfMatchPreventionInstruction : BitVec 8
  pad3 : Alpha 3
  marketSegmentId : BitVec 32
  pad4 : Alpha 4
  securityId : BitVec 64
  orderQty : BitVec 64
  price : BitVec 64
  side : BitVec 8
  execInst : BitVec 8
  timeInForce : BitVec 8
  pad1 : Alpha 1
  checkSumCorrection : BitVec 16
  pad2v3 : Alpha 2
  legOrdGrpComp : Bounded 1 LegOrdGrpComp
  deriving DecidableEq, Repr

namespace ModifyOrderRequest

def encode (message : ModifyOrderRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 8 message.origClOrdId
    ++ (encodeUIntLE 8 message.stopPx
    ++ (encodeUIntLE 8 message.partyIdClientId
    ++ (encodeUIntLE 8 message.executingTrader
    ++ (encodeUIntLE 4 message.matchInstCrossId
    ++ (encodeUIntLE 4 message.expireDate
    ++ (encodeUIntLE 4 message.targetPartyIdSessionId
    ++ (encodeUInt 1 message.tradingSessionSubId
    ++ (encodeUInt 1 message.ownershipIndicator
    ++ (encodeUInt 1 message.applSeqIndicator
    ++ (encodeUInt 1 message.ordType
    ++ (encodeUInt 1 message.priceValidityCheckType
    ++ (encodeUInt 1 message.valueCheckTypeValue
    ++ (encodeUInt 1 message.orderOrigination
    ++ (Alpha.encode message.partyIdTakeUpTradingFirm
    ++ (Alpha.encode message.partyIdOrderOriginationFirm
    ++ (Alpha.encode message.partyIdBeneficiary
    ++ (Alpha.encode message.account
    ++ (Alpha.encode message.partyIdPositionAccount
    ++ (PositionEffect.encode message.positionEffect
    ++ (Alpha.encode message.partyIdLocationId
    ++ (CustOrderHandlingInst.encode message.custOrderHandlingInst
    ++ (Alpha.encode message.complianceText
    ++ (Alpha.encode message.freeText1
    ++ (Alpha.encode message.freeText2
    ++ (Alpha.encode message.freeText3
    ++ (Alpha.encode message.fixClOrdId
    ++ (Alpha.encode message.partyEndClientIdentification
    ++ (encodeUInt 1 message.executingTraderQualifier
    ++ (encodeUInt 1 message.partyIdInvestmentDecisionMakerQualifier
    ++ (encodeUIntLE 8 message.partyIdInvestmentDecisionMaker
    ++ (encodeUInt 1 message.orderAttributeLiquidityProvision
    ++ (encodeUInt 1 message.tradingCapacity
    ++ (encodeUInt 1 message.productComplex
    ++ (encodeUInt 1 message.selfMatchPreventionInstruction
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.legOrdGrpComp.val.length)
    ++ (Alpha.encode message.pad3
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (Alpha.encode message.pad4
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.orderQty
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUInt 1 message.side
    ++ (encodeUInt 1 message.execInst
    ++ (encodeUInt 1 message.timeInForce
    ++ (Alpha.encode message.pad1
    ++ (encodeUIntLE 2 message.checkSumCorrection
    ++ (Alpha.encode message.pad2v3
    ++ (encodeMany LegOrdGrpComp.encode message.legOrdGrpComp.val)))))))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (ModifyOrderRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (origClOrdId, bytes) ← decodeUIntLE 8 bytes
  let (stopPx, bytes) ← decodeUIntLE 8 bytes
  let (partyIdClientId, bytes) ← decodeUIntLE 8 bytes
  let (executingTrader, bytes) ← decodeUIntLE 8 bytes
  let (matchInstCrossId, bytes) ← decodeUIntLE 4 bytes
  let (expireDate, bytes) ← decodeUIntLE 4 bytes
  let (targetPartyIdSessionId, bytes) ← decodeUIntLE 4 bytes
  let (tradingSessionSubId, bytes) ← decodeUInt 1 bytes
  let (ownershipIndicator, bytes) ← decodeUInt 1 bytes
  let (applSeqIndicator, bytes) ← decodeUInt 1 bytes
  let (ordType, bytes) ← decodeUInt 1 bytes
  let (priceValidityCheckType, bytes) ← decodeUInt 1 bytes
  let (valueCheckTypeValue, bytes) ← decodeUInt 1 bytes
  let (orderOrigination, bytes) ← decodeUInt 1 bytes
  let (partyIdTakeUpTradingFirm, bytes) ← Alpha.decode 5 bytes
  let (partyIdOrderOriginationFirm, bytes) ← Alpha.decode 7 bytes
  let (partyIdBeneficiary, bytes) ← Alpha.decode 9 bytes
  let (account, bytes) ← Alpha.decode 2 bytes
  let (partyIdPositionAccount, bytes) ← Alpha.decode 32 bytes
  let (positionEffect, bytes) ← PositionEffect.decode bytes
  let (partyIdLocationId, bytes) ← Alpha.decode 2 bytes
  let (custOrderHandlingInst, bytes) ← CustOrderHandlingInst.decode bytes
  let (complianceText, bytes) ← Alpha.decode 20 bytes
  let (freeText1, bytes) ← Alpha.decode 12 bytes
  let (freeText2, bytes) ← Alpha.decode 12 bytes
  let (freeText3, bytes) ← Alpha.decode 12 bytes
  let (fixClOrdId, bytes) ← Alpha.decode 20 bytes
  let (partyEndClientIdentification, bytes) ← Alpha.decode 20 bytes
  let (executingTraderQualifier, bytes) ← decodeUInt 1 bytes
  let (partyIdInvestmentDecisionMakerQualifier, bytes) ← decodeUInt 1 bytes
  let (partyIdInvestmentDecisionMaker, bytes) ← decodeUIntLE 8 bytes
  let (orderAttributeLiquidityProvision, bytes) ← decodeUInt 1 bytes
  let (tradingCapacity, bytes) ← decodeUInt 1 bytes
  let (productComplex, bytes) ← decodeUInt 1 bytes
  let (selfMatchPreventionInstruction, bytes) ← decodeUInt 1 bytes
  let (noLegOnbooks, bytes) ← decodeUInt 1 bytes
  let (pad3, bytes) ← Alpha.decode 3 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (pad4, bytes) ← Alpha.decode 4 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (orderQty, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (execInst, bytes) ← decodeUInt 1 bytes
  let (timeInForce, bytes) ← decodeUInt 1 bytes
  let (pad1, bytes) ← Alpha.decode 1 bytes
  let (checkSumCorrection, bytes) ← decodeUIntLE 2 bytes
  let (pad2v3, bytes) ← Alpha.decode 2 bytes
  let (legOrdGrpComp_, bytes) ← decodeMany LegOrdGrpComp.decode noLegOnbooks.toNat bytes
  if fits_legOrdGrpComp : legOrdGrpComp_.length < 256 ^ 1 then
    pure ({ networkMsgId, pad2, requestHeaderComp, orderId, clOrdId, origClOrdId, stopPx, partyIdClientId, executingTrader, matchInstCrossId, expireDate, targetPartyIdSessionId, tradingSessionSubId, ownershipIndicator, applSeqIndicator, ordType, priceValidityCheckType, valueCheckTypeValue, orderOrigination, partyIdTakeUpTradingFirm, partyIdOrderOriginationFirm, partyIdBeneficiary, account, partyIdPositionAccount, positionEffect, partyIdLocationId, custOrderHandlingInst, complianceText, freeText1, freeText2, freeText3, fixClOrdId, partyEndClientIdentification, executingTraderQualifier, partyIdInvestmentDecisionMakerQualifier, partyIdInvestmentDecisionMaker, orderAttributeLiquidityProvision, tradingCapacity, productComplex, selfMatchPreventionInstruction, pad3, marketSegmentId, pad4, securityId, orderQty, price, side, execInst, timeInForce, pad1, checkSumCorrection, pad2v3, legOrdGrpComp := ⟨legOrdGrpComp_, fits_legOrdGrpComp⟩ }, bytes)
  else none

theorem encode_length_pos (message : ModifyOrderRequest) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ModifyOrderRequest) : (encode message).length ≤ 2338 := by
  have bound_legOrdGrpComp := message.legOrdGrpComp.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length, PositionEffect.encode_length, CustOrderHandlingInst.encode_length, encodeMany_length_const LegOrdGrpComp.encode 8 LegOrdGrpComp.encode_length]
  omega

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : ModifyOrderRequest) (rest : List UInt8) :
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
  rw [List.append_assoc, PositionEffect.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CustOrderHandlingInst.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 LegOrdGrpComp.encode LegOrdGrpComp.decode LegOrdGrpComp.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.legOrdGrpComp.length_lt]
  rfl

end ModifyOrderRequest

/-- Modify Order Short Request: 138 bytes -/
structure ModifyOrderShortRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  clOrdId : BitVec 64
  origClOrdId : BitVec 64
  partyIdClientId : BitVec 64
  executingTrader : BitVec 64
  matchInstCrossId : BitVec 32
  applSeqIndicator : BitVec 8
  priceValidityCheckType : BitVec 8
  valueCheckTypeValue : BitVec 8
  tradingCapacity : BitVec 8
  orderOrigination : BitVec 8
  executingTraderQualifier : BitVec 8
  partyIdInvestmentDecisionMakerQualifier : BitVec 8
  complianceText : Alpha 20
  pad1v2 : Alpha 1
  partyIdInvestmentDecisionMaker : BitVec 64
  enrichmentRuleId : BitVec 16
  orderAttributeLiquidityProvision : BitVec 8
  productComplex : BitVec 8
  selfMatchPreventionInstruction : BitVec 8
  pad3 : Alpha 3
  marketSegmentId : BitVec 32
  pad4v1 : Alpha 4
  securityId : BitVec 64
  orderQty : BitVec 64
  price : BitVec 64
  side : BitVec 8
  execInst : BitVec 8
  timeInForce : BitVec 8
  pad1v1 : Alpha 1
  checkSumCorrection : BitVec 16
  pad2v2 : Alpha 2
  deriving DecidableEq, Repr

namespace ModifyOrderShortRequest

def encode (message : ModifyOrderShortRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 8 message.origClOrdId
    ++ (encodeUIntLE 8 message.partyIdClientId
    ++ (encodeUIntLE 8 message.executingTrader
    ++ (encodeUIntLE 4 message.matchInstCrossId
    ++ (encodeUInt 1 message.applSeqIndicator
    ++ (encodeUInt 1 message.priceValidityCheckType
    ++ (encodeUInt 1 message.valueCheckTypeValue
    ++ (encodeUInt 1 message.tradingCapacity
    ++ (encodeUInt 1 message.orderOrigination
    ++ (encodeUInt 1 message.executingTraderQualifier
    ++ (encodeUInt 1 message.partyIdInvestmentDecisionMakerQualifier
    ++ (Alpha.encode message.complianceText
    ++ (Alpha.encode message.pad1v2
    ++ (encodeUIntLE 8 message.partyIdInvestmentDecisionMaker
    ++ (encodeUIntLE 2 message.enrichmentRuleId
    ++ (encodeUInt 1 message.orderAttributeLiquidityProvision
    ++ (encodeUInt 1 message.productComplex
    ++ (encodeUInt 1 message.selfMatchPreventionInstruction
    ++ (Alpha.encode message.pad3
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (Alpha.encode message.pad4v1
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.orderQty
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUInt 1 message.side
    ++ (encodeUInt 1 message.execInst
    ++ (encodeUInt 1 message.timeInForce
    ++ (Alpha.encode message.pad1v1
    ++ (encodeUIntLE 2 message.checkSumCorrection
    ++ (Alpha.encode message.pad2v2)))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (ModifyOrderShortRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (origClOrdId, bytes) ← decodeUIntLE 8 bytes
  let (partyIdClientId, bytes) ← decodeUIntLE 8 bytes
  let (executingTrader, bytes) ← decodeUIntLE 8 bytes
  let (matchInstCrossId, bytes) ← decodeUIntLE 4 bytes
  let (applSeqIndicator, bytes) ← decodeUInt 1 bytes
  let (priceValidityCheckType, bytes) ← decodeUInt 1 bytes
  let (valueCheckTypeValue, bytes) ← decodeUInt 1 bytes
  let (tradingCapacity, bytes) ← decodeUInt 1 bytes
  let (orderOrigination, bytes) ← decodeUInt 1 bytes
  let (executingTraderQualifier, bytes) ← decodeUInt 1 bytes
  let (partyIdInvestmentDecisionMakerQualifier, bytes) ← decodeUInt 1 bytes
  let (complianceText, bytes) ← Alpha.decode 20 bytes
  let (pad1v2, bytes) ← Alpha.decode 1 bytes
  let (partyIdInvestmentDecisionMaker, bytes) ← decodeUIntLE 8 bytes
  let (enrichmentRuleId, bytes) ← decodeUIntLE 2 bytes
  let (orderAttributeLiquidityProvision, bytes) ← decodeUInt 1 bytes
  let (productComplex, bytes) ← decodeUInt 1 bytes
  let (selfMatchPreventionInstruction, bytes) ← decodeUInt 1 bytes
  let (pad3, bytes) ← Alpha.decode 3 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (pad4v1, bytes) ← Alpha.decode 4 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (orderQty, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (execInst, bytes) ← decodeUInt 1 bytes
  let (timeInForce, bytes) ← decodeUInt 1 bytes
  let (pad1v1, bytes) ← Alpha.decode 1 bytes
  let (checkSumCorrection, bytes) ← decodeUIntLE 2 bytes
  let (pad2v2, bytes) ← Alpha.decode 2 bytes
  pure ({ networkMsgId, pad2, requestHeaderComp, clOrdId, origClOrdId, partyIdClientId, executingTrader, matchInstCrossId, applSeqIndicator, priceValidityCheckType, valueCheckTypeValue, tradingCapacity, orderOrigination, executingTraderQualifier, partyIdInvestmentDecisionMakerQualifier, complianceText, pad1v2, partyIdInvestmentDecisionMaker, enrichmentRuleId, orderAttributeLiquidityProvision, productComplex, selfMatchPreventionInstruction, pad3, marketSegmentId, pad4v1, securityId, orderQty, price, side, execInst, timeInForce, pad1v1, checkSumCorrection, pad2v2 }, bytes)

@[simp] theorem encode_length (message : ModifyOrderShortRequest) : (encode message).length = 138 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : ModifyOrderShortRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : ModifyOrderShortRequest) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ModifyOrderShortRequest

/-- Modify Order Single Request: 290 bytes -/
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
  stopPx : BitVec 64
  partyIdClientId : BitVec 64
  partyIdInvestmentDecisionMaker : BitVec 64
  executingTrader : BitVec 64
  expireDate : BitVec 32
  marketSegmentId : BitVec 32
  matchInstCrossId : BitVec 32
  targetPartyIdSessionId : BitVec 32
  selfMatchPreventionInstruction : BitVec 8
  partyIdTakeUpTradingFirm : Alpha 5
  partyIdOrderOriginationFirm : Alpha 7
  partyIdBeneficiary : Alpha 9
  applSeqIndicator : BitVec 8
  productComplex : BitVec 8
  side : BitVec 8
  ordType : BitVec 8
  priceValidityCheckType : BitVec 8
  valueCheckTypeValue : BitVec 8
  orderAttributeLiquidityProvision : BitVec 8
  timeInForce : BitVec 8
  execInst : BitVec 8
  tradingSessionSubId : BitVec 8
  tradingCapacity : BitVec 8
  orderOrigination : BitVec 8
  partyIdInvestmentDecisionMakerQualifier : BitVec 8
  executingTraderQualifier : BitVec 8
  account : Alpha 2
  partyIdPositionAccount : Alpha 32
  positionEffect : PositionEffect
  ownershipIndicator : BitVec 8
  partyIdLocationId : Alpha 2
  custOrderHandlingInst : CustOrderHandlingInst
  complianceText : Alpha 20
  freeText1 : Alpha 12
  freeText2 : Alpha 12
  freeText3 : Alpha 12
  fixClOrdId : Alpha 20
  partyEndClientIdentification : Alpha 20
  pad5 : Alpha 5
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
    ++ (encodeUIntLE 8 message.stopPx
    ++ (encodeUIntLE 8 message.partyIdClientId
    ++ (encodeUIntLE 8 message.partyIdInvestmentDecisionMaker
    ++ (encodeUIntLE 8 message.executingTrader
    ++ (encodeUIntLE 4 message.expireDate
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.matchInstCrossId
    ++ (encodeUIntLE 4 message.targetPartyIdSessionId
    ++ (encodeUInt 1 message.selfMatchPreventionInstruction
    ++ (Alpha.encode message.partyIdTakeUpTradingFirm
    ++ (Alpha.encode message.partyIdOrderOriginationFirm
    ++ (Alpha.encode message.partyIdBeneficiary
    ++ (encodeUInt 1 message.applSeqIndicator
    ++ (encodeUInt 1 message.productComplex
    ++ (encodeUInt 1 message.side
    ++ (encodeUInt 1 message.ordType
    ++ (encodeUInt 1 message.priceValidityCheckType
    ++ (encodeUInt 1 message.valueCheckTypeValue
    ++ (encodeUInt 1 message.orderAttributeLiquidityProvision
    ++ (encodeUInt 1 message.timeInForce
    ++ (encodeUInt 1 message.execInst
    ++ (encodeUInt 1 message.tradingSessionSubId
    ++ (encodeUInt 1 message.tradingCapacity
    ++ (encodeUInt 1 message.orderOrigination
    ++ (encodeUInt 1 message.partyIdInvestmentDecisionMakerQualifier
    ++ (encodeUInt 1 message.executingTraderQualifier
    ++ (Alpha.encode message.account
    ++ (Alpha.encode message.partyIdPositionAccount
    ++ (PositionEffect.encode message.positionEffect
    ++ (encodeUInt 1 message.ownershipIndicator
    ++ (Alpha.encode message.partyIdLocationId
    ++ (CustOrderHandlingInst.encode message.custOrderHandlingInst
    ++ (Alpha.encode message.complianceText
    ++ (Alpha.encode message.freeText1
    ++ (Alpha.encode message.freeText2
    ++ (Alpha.encode message.freeText3
    ++ (Alpha.encode message.fixClOrdId
    ++ (Alpha.encode message.partyEndClientIdentification
    ++ (Alpha.encode message.pad5)))))))))))))))))))))))))))))))))))))))))))))))

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
  let (stopPx, bytes) ← decodeUIntLE 8 bytes
  let (partyIdClientId, bytes) ← decodeUIntLE 8 bytes
  let (partyIdInvestmentDecisionMaker, bytes) ← decodeUIntLE 8 bytes
  let (executingTrader, bytes) ← decodeUIntLE 8 bytes
  let (expireDate, bytes) ← decodeUIntLE 4 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (matchInstCrossId, bytes) ← decodeUIntLE 4 bytes
  let (targetPartyIdSessionId, bytes) ← decodeUIntLE 4 bytes
  let (selfMatchPreventionInstruction, bytes) ← decodeUInt 1 bytes
  let (partyIdTakeUpTradingFirm, bytes) ← Alpha.decode 5 bytes
  let (partyIdOrderOriginationFirm, bytes) ← Alpha.decode 7 bytes
  let (partyIdBeneficiary, bytes) ← Alpha.decode 9 bytes
  let (applSeqIndicator, bytes) ← decodeUInt 1 bytes
  let (productComplex, bytes) ← decodeUInt 1 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (ordType, bytes) ← decodeUInt 1 bytes
  let (priceValidityCheckType, bytes) ← decodeUInt 1 bytes
  let (valueCheckTypeValue, bytes) ← decodeUInt 1 bytes
  let (orderAttributeLiquidityProvision, bytes) ← decodeUInt 1 bytes
  let (timeInForce, bytes) ← decodeUInt 1 bytes
  let (execInst, bytes) ← decodeUInt 1 bytes
  let (tradingSessionSubId, bytes) ← decodeUInt 1 bytes
  let (tradingCapacity, bytes) ← decodeUInt 1 bytes
  let (orderOrigination, bytes) ← decodeUInt 1 bytes
  let (partyIdInvestmentDecisionMakerQualifier, bytes) ← decodeUInt 1 bytes
  let (executingTraderQualifier, bytes) ← decodeUInt 1 bytes
  let (account, bytes) ← Alpha.decode 2 bytes
  let (partyIdPositionAccount, bytes) ← Alpha.decode 32 bytes
  let (positionEffect, bytes) ← PositionEffect.decode bytes
  let (ownershipIndicator, bytes) ← decodeUInt 1 bytes
  let (partyIdLocationId, bytes) ← Alpha.decode 2 bytes
  let (custOrderHandlingInst, bytes) ← CustOrderHandlingInst.decode bytes
  let (complianceText, bytes) ← Alpha.decode 20 bytes
  let (freeText1, bytes) ← Alpha.decode 12 bytes
  let (freeText2, bytes) ← Alpha.decode 12 bytes
  let (freeText3, bytes) ← Alpha.decode 12 bytes
  let (fixClOrdId, bytes) ← Alpha.decode 20 bytes
  let (partyEndClientIdentification, bytes) ← Alpha.decode 20 bytes
  let (pad5, bytes) ← Alpha.decode 5 bytes
  pure ({ networkMsgId, pad2, requestHeaderComp, orderId, clOrdId, origClOrdId, securityId, price, orderQty, stopPx, partyIdClientId, partyIdInvestmentDecisionMaker, executingTrader, expireDate, marketSegmentId, matchInstCrossId, targetPartyIdSessionId, selfMatchPreventionInstruction, partyIdTakeUpTradingFirm, partyIdOrderOriginationFirm, partyIdBeneficiary, applSeqIndicator, productComplex, side, ordType, priceValidityCheckType, valueCheckTypeValue, orderAttributeLiquidityProvision, timeInForce, execInst, tradingSessionSubId, tradingCapacity, orderOrigination, partyIdInvestmentDecisionMakerQualifier, executingTraderQualifier, account, partyIdPositionAccount, positionEffect, ownershipIndicator, partyIdLocationId, custOrderHandlingInst, complianceText, freeText1, freeText2, freeText3, fixClOrdId, partyEndClientIdentification, pad5 }, bytes)

@[simp] theorem encode_length (message : ModifyOrderSingleRequest) : (encode message).length = 290 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length, PositionEffect.encode_length, CustOrderHandlingInst.encode_length]

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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, PositionEffect.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CustOrderHandlingInst.decode_encode, some_bind]
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

/-- Modify Order Single Short Request: 122 bytes -/
structure ModifyOrderSingleShortRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  clOrdId : BitVec 64
  origClOrdId : BitVec 64
  price : BitVec 64
  orderQty : BitVec 64
  partyIdClientId : BitVec 64
  partyIdInvestmentDecisionMaker : BitVec 64
  executingTrader : BitVec 64
  simpleSecurityId : BitVec 32
  matchInstCrossId : BitVec 32
  enrichmentRuleId : BitVec 16
  selfMatchPreventionInstruction : BitVec 8
  side : BitVec 8
  priceValidityCheckType : BitVec 8
  valueCheckTypeValue : BitVec 8
  orderAttributeLiquidityProvision : BitVec 8
  timeInForce : BitVec 8
  applSeqIndicator : BitVec 8
  execInst : BitVec 8
  tradingCapacity : BitVec 8
  orderOrigination : BitVec 8
  partyIdInvestmentDecisionMakerQualifier : BitVec 8
  executingTraderQualifier : BitVec 8
  complianceText : Alpha 20
  pad6 : Alpha 6
  deriving DecidableEq, Repr

namespace ModifyOrderSingleShortRequest

def encode (message : ModifyOrderSingleShortRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 8 message.origClOrdId
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 8 message.orderQty
    ++ (encodeUIntLE 8 message.partyIdClientId
    ++ (encodeUIntLE 8 message.partyIdInvestmentDecisionMaker
    ++ (encodeUIntLE 8 message.executingTrader
    ++ (encodeUIntLE 4 message.simpleSecurityId
    ++ (encodeUIntLE 4 message.matchInstCrossId
    ++ (encodeUIntLE 2 message.enrichmentRuleId
    ++ (encodeUInt 1 message.selfMatchPreventionInstruction
    ++ (encodeUInt 1 message.side
    ++ (encodeUInt 1 message.priceValidityCheckType
    ++ (encodeUInt 1 message.valueCheckTypeValue
    ++ (encodeUInt 1 message.orderAttributeLiquidityProvision
    ++ (encodeUInt 1 message.timeInForce
    ++ (encodeUInt 1 message.applSeqIndicator
    ++ (encodeUInt 1 message.execInst
    ++ (encodeUInt 1 message.tradingCapacity
    ++ (encodeUInt 1 message.orderOrigination
    ++ (encodeUInt 1 message.partyIdInvestmentDecisionMakerQualifier
    ++ (encodeUInt 1 message.executingTraderQualifier
    ++ (Alpha.encode message.complianceText
    ++ (Alpha.encode message.pad6))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (ModifyOrderSingleShortRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (origClOrdId, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (orderQty, bytes) ← decodeUIntLE 8 bytes
  let (partyIdClientId, bytes) ← decodeUIntLE 8 bytes
  let (partyIdInvestmentDecisionMaker, bytes) ← decodeUIntLE 8 bytes
  let (executingTrader, bytes) ← decodeUIntLE 8 bytes
  let (simpleSecurityId, bytes) ← decodeUIntLE 4 bytes
  let (matchInstCrossId, bytes) ← decodeUIntLE 4 bytes
  let (enrichmentRuleId, bytes) ← decodeUIntLE 2 bytes
  let (selfMatchPreventionInstruction, bytes) ← decodeUInt 1 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (priceValidityCheckType, bytes) ← decodeUInt 1 bytes
  let (valueCheckTypeValue, bytes) ← decodeUInt 1 bytes
  let (orderAttributeLiquidityProvision, bytes) ← decodeUInt 1 bytes
  let (timeInForce, bytes) ← decodeUInt 1 bytes
  let (applSeqIndicator, bytes) ← decodeUInt 1 bytes
  let (execInst, bytes) ← decodeUInt 1 bytes
  let (tradingCapacity, bytes) ← decodeUInt 1 bytes
  let (orderOrigination, bytes) ← decodeUInt 1 bytes
  let (partyIdInvestmentDecisionMakerQualifier, bytes) ← decodeUInt 1 bytes
  let (executingTraderQualifier, bytes) ← decodeUInt 1 bytes
  let (complianceText, bytes) ← Alpha.decode 20 bytes
  let (pad6, bytes) ← Alpha.decode 6 bytes
  pure ({ networkMsgId, pad2, requestHeaderComp, clOrdId, origClOrdId, price, orderQty, partyIdClientId, partyIdInvestmentDecisionMaker, executingTrader, simpleSecurityId, matchInstCrossId, enrichmentRuleId, selfMatchPreventionInstruction, side, priceValidityCheckType, valueCheckTypeValue, orderAttributeLiquidityProvision, timeInForce, applSeqIndicator, execInst, tradingCapacity, orderOrigination, partyIdInvestmentDecisionMakerQualifier, executingTraderQualifier, complianceText, pad6 }, bytes)

@[simp] theorem encode_length (message : ModifyOrderSingleShortRequest) : (encode message).length = 122 := by
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  relatedClosePrice : BitVec 64
  relatedPx : BitVec 64
  marketSegmentId : BitVec 32
  packageId : BitVec 32
  tesExecId : BitVec 32
  relatedMarketSegmentId : BitVec 32
  trdType : BitVec 16
  tradeReportType : BitVec 8
  tradePublishIndicator : BitVec 8
  swapClearer : BitVec 8
  tradeReportText : Alpha 20
  tradeReportId : Alpha 20
  pad1 : Alpha 1
  sideAllocGrpComp : Bounded 1 SideAllocGrpComp
  trdInstrmntLegGrpComp : Bounded 1 TrdInstrmntLegGrpComp
  deriving DecidableEq, Repr

namespace ModifyTesTradeRequest

def encode (message : ModifyTesTradeRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 8 message.lastPx
    ++ (encodeUIntLE 8 message.transBkdTime
    ++ (encodeUIntLE 8 message.relatedClosePrice
    ++ (encodeUIntLE 8 message.relatedPx
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.packageId
    ++ (encodeUIntLE 4 message.tesExecId
    ++ (encodeUIntLE 4 message.relatedMarketSegmentId
    ++ (encodeUIntLE 2 message.trdType
    ++ (encodeUInt 1 message.tradeReportType
    ++ (encodeUInt 1 message.tradePublishIndicator
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.sideAllocGrpComp.val.length)
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.trdInstrmntLegGrpComp.val.length)
    ++ (encodeUInt 1 message.swapClearer
    ++ (Alpha.encode message.tradeReportText
    ++ (Alpha.encode message.tradeReportId
    ++ (Alpha.encode message.pad1
    ++ (encodeMany SideAllocGrpComp.encode message.sideAllocGrpComp.val
    ++ (encodeMany TrdInstrmntLegGrpComp.encode message.trdInstrmntLegGrpComp.val)))))))))))))))))))))

def decode (bytes : List UInt8) : Option (ModifyTesTradeRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  let (transBkdTime, bytes) ← decodeUIntLE 8 bytes
  let (relatedClosePrice, bytes) ← decodeUIntLE 8 bytes
  let (relatedPx, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (packageId, bytes) ← decodeUIntLE 4 bytes
  let (tesExecId, bytes) ← decodeUIntLE 4 bytes
  let (relatedMarketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (trdType, bytes) ← decodeUIntLE 2 bytes
  let (tradeReportType, bytes) ← decodeUInt 1 bytes
  let (tradePublishIndicator, bytes) ← decodeUInt 1 bytes
  let (noSideAllocs, bytes) ← decodeUInt 1 bytes
  let (noLegs, bytes) ← decodeUInt 1 bytes
  let (swapClearer, bytes) ← decodeUInt 1 bytes
  let (tradeReportText, bytes) ← Alpha.decode 20 bytes
  let (tradeReportId, bytes) ← Alpha.decode 20 bytes
  let (pad1, bytes) ← Alpha.decode 1 bytes
  let (sideAllocGrpComp_, bytes) ← decodeMany SideAllocGrpComp.decode noSideAllocs.toNat bytes
  let (trdInstrmntLegGrpComp_, bytes) ← decodeMany TrdInstrmntLegGrpComp.decode noLegs.toNat bytes
  if fits_sideAllocGrpComp : sideAllocGrpComp_.length < 256 ^ 1 then
    if fits_trdInstrmntLegGrpComp : trdInstrmntLegGrpComp_.length < 256 ^ 1 then
      pure ({ networkMsgId, pad2, requestHeaderComp, lastPx, transBkdTime, relatedClosePrice, relatedPx, marketSegmentId, packageId, tesExecId, relatedMarketSegmentId, trdType, tradeReportType, tradePublishIndicator, swapClearer, tradeReportText, tradeReportId, pad1, sideAllocGrpComp := ⟨sideAllocGrpComp_, fits_sideAllocGrpComp⟩, trdInstrmntLegGrpComp := ⟨trdInstrmntLegGrpComp_, fits_trdInstrmntLegGrpComp⟩ }, bytes)
    else none
  else none

theorem encode_length_pos (message : ModifyTesTradeRequest) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ModifyTesTradeRequest) : (encode message).length ≤ 14394 := by
  have bound_sideAllocGrpComp := message.sideAllocGrpComp.length_lt
  have bound_trdInstrmntLegGrpComp := message.trdInstrmntLegGrpComp.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const SideAllocGrpComp.encode 32 SideAllocGrpComp.encode_length, encodeMany_length_const TrdInstrmntLegGrpComp.encode 24 TrdInstrmntLegGrpComp.encode_length]
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
  rw [List.append_assoc, decodeMany_bounded 1 SideAllocGrpComp.encode SideAllocGrpComp.decode SideAllocGrpComp.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 TrdInstrmntLegGrpComp.encode TrdInstrmntLegGrpComp.decode TrdInstrmntLegGrpComp.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.sideAllocGrpComp.length_lt, dite_eq_left message.trdInstrmntLegGrpComp.length_lt]
  rfl

end ModifyTesTradeRequest

/-- New Order Complex Request -/
structure NewOrderComplexRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  clOrdId : BitVec 64
  securityId : BitVec 64
  price : BitVec 64
  orderQty : BitVec 64
  partyIdClientId : BitVec 64
  partyIdInvestmentDecisionMaker : BitVec 64
  executingTrader : BitVec 64
  marketSegmentId : BitVec 32
  expireDate : BitVec 32
  matchInstCrossId : BitVec 32
  partyIdTakeUpTradingFirm : Alpha 5
  partyIdOrderOriginationFirm : Alpha 7
  partyIdBeneficiary : Alpha 9
  applSeqIndicator : BitVec 8
  selfMatchPreventionInstruction : BitVec 8
  productComplex : BitVec 8
  side : BitVec 8
  ordType : BitVec 8
  priceValidityCheckType : BitVec 8
  valueCheckTypeValue : BitVec 8
  orderAttributeLiquidityProvision : BitVec 8
  orderAttributeRiskReduction : BitVec 8
  execInst : BitVec 8
  timeInForce : BitVec 8
  tradingCapacity : BitVec 8
  orderOrigination : BitVec 8
  partyIdInvestmentDecisionMakerQualifier : BitVec 8
  executingTraderQualifier : BitVec 8
  partyIdLocationId : Alpha 2
  complianceText : Alpha 20
  custOrderHandlingInst : CustOrderHandlingInst
  partyIdPositionAccount : Alpha 32
  freeText1 : Alpha 12
  freeText2 : Alpha 12
  freeText3 : Alpha 12
  fixClOrdId : Alpha 20
  partyEndClientIdentification : Alpha 20
  pad4 : Alpha 4
  legOrdGrpComp : Bounded 1 LegOrdGrpComp
  deriving DecidableEq, Repr

namespace NewOrderComplexRequest

def encode (message : NewOrderComplexRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 8 message.orderQty
    ++ (encodeUIntLE 8 message.partyIdClientId
    ++ (encodeUIntLE 8 message.partyIdInvestmentDecisionMaker
    ++ (encodeUIntLE 8 message.executingTrader
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.expireDate
    ++ (encodeUIntLE 4 message.matchInstCrossId
    ++ (Alpha.encode message.partyIdTakeUpTradingFirm
    ++ (Alpha.encode message.partyIdOrderOriginationFirm
    ++ (Alpha.encode message.partyIdBeneficiary
    ++ (encodeUInt 1 message.applSeqIndicator
    ++ (encodeUInt 1 message.selfMatchPreventionInstruction
    ++ (encodeUInt 1 message.productComplex
    ++ (encodeUInt 1 message.side
    ++ (encodeUInt 1 message.ordType
    ++ (encodeUInt 1 message.priceValidityCheckType
    ++ (encodeUInt 1 message.valueCheckTypeValue
    ++ (encodeUInt 1 message.orderAttributeLiquidityProvision
    ++ (encodeUInt 1 message.orderAttributeRiskReduction
    ++ (encodeUInt 1 message.execInst
    ++ (encodeUInt 1 message.timeInForce
    ++ (encodeUInt 1 message.tradingCapacity
    ++ (encodeUInt 1 message.orderOrigination
    ++ (encodeUInt 1 message.partyIdInvestmentDecisionMakerQualifier
    ++ (encodeUInt 1 message.executingTraderQualifier
    ++ (Alpha.encode message.partyIdLocationId
    ++ (Alpha.encode message.complianceText
    ++ (CustOrderHandlingInst.encode message.custOrderHandlingInst
    ++ (Alpha.encode message.partyIdPositionAccount
    ++ (Alpha.encode message.freeText1
    ++ (Alpha.encode message.freeText2
    ++ (Alpha.encode message.freeText3
    ++ (Alpha.encode message.fixClOrdId
    ++ (Alpha.encode message.partyEndClientIdentification
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.legOrdGrpComp.val.length)
    ++ (Alpha.encode message.pad4
    ++ (encodeMany LegOrdGrpComp.encode message.legOrdGrpComp.val))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (NewOrderComplexRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (orderQty, bytes) ← decodeUIntLE 8 bytes
  let (partyIdClientId, bytes) ← decodeUIntLE 8 bytes
  let (partyIdInvestmentDecisionMaker, bytes) ← decodeUIntLE 8 bytes
  let (executingTrader, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (expireDate, bytes) ← decodeUIntLE 4 bytes
  let (matchInstCrossId, bytes) ← decodeUIntLE 4 bytes
  let (partyIdTakeUpTradingFirm, bytes) ← Alpha.decode 5 bytes
  let (partyIdOrderOriginationFirm, bytes) ← Alpha.decode 7 bytes
  let (partyIdBeneficiary, bytes) ← Alpha.decode 9 bytes
  let (applSeqIndicator, bytes) ← decodeUInt 1 bytes
  let (selfMatchPreventionInstruction, bytes) ← decodeUInt 1 bytes
  let (productComplex, bytes) ← decodeUInt 1 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (ordType, bytes) ← decodeUInt 1 bytes
  let (priceValidityCheckType, bytes) ← decodeUInt 1 bytes
  let (valueCheckTypeValue, bytes) ← decodeUInt 1 bytes
  let (orderAttributeLiquidityProvision, bytes) ← decodeUInt 1 bytes
  let (orderAttributeRiskReduction, bytes) ← decodeUInt 1 bytes
  let (execInst, bytes) ← decodeUInt 1 bytes
  let (timeInForce, bytes) ← decodeUInt 1 bytes
  let (tradingCapacity, bytes) ← decodeUInt 1 bytes
  let (orderOrigination, bytes) ← decodeUInt 1 bytes
  let (partyIdInvestmentDecisionMakerQualifier, bytes) ← decodeUInt 1 bytes
  let (executingTraderQualifier, bytes) ← decodeUInt 1 bytes
  let (partyIdLocationId, bytes) ← Alpha.decode 2 bytes
  let (complianceText, bytes) ← Alpha.decode 20 bytes
  let (custOrderHandlingInst, bytes) ← CustOrderHandlingInst.decode bytes
  let (partyIdPositionAccount, bytes) ← Alpha.decode 32 bytes
  let (freeText1, bytes) ← Alpha.decode 12 bytes
  let (freeText2, bytes) ← Alpha.decode 12 bytes
  let (freeText3, bytes) ← Alpha.decode 12 bytes
  let (fixClOrdId, bytes) ← Alpha.decode 20 bytes
  let (partyEndClientIdentification, bytes) ← Alpha.decode 20 bytes
  let (noLegOnbooks, bytes) ← decodeUInt 1 bytes
  let (pad4, bytes) ← Alpha.decode 4 bytes
  let (legOrdGrpComp_, bytes) ← decodeMany LegOrdGrpComp.decode noLegOnbooks.toNat bytes
  if fits_legOrdGrpComp : legOrdGrpComp_.length < 256 ^ 1 then
    pure ({ networkMsgId, pad2, requestHeaderComp, clOrdId, securityId, price, orderQty, partyIdClientId, partyIdInvestmentDecisionMaker, executingTrader, marketSegmentId, expireDate, matchInstCrossId, partyIdTakeUpTradingFirm, partyIdOrderOriginationFirm, partyIdBeneficiary, applSeqIndicator, selfMatchPreventionInstruction, productComplex, side, ordType, priceValidityCheckType, valueCheckTypeValue, orderAttributeLiquidityProvision, orderAttributeRiskReduction, execInst, timeInForce, tradingCapacity, orderOrigination, partyIdInvestmentDecisionMakerQualifier, executingTraderQualifier, partyIdLocationId, complianceText, custOrderHandlingInst, partyIdPositionAccount, freeText1, freeText2, freeText3, fixClOrdId, partyEndClientIdentification, pad4, legOrdGrpComp := ⟨legOrdGrpComp_, fits_legOrdGrpComp⟩ }, bytes)
  else none

theorem encode_length_pos (message : NewOrderComplexRequest) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : NewOrderComplexRequest) : (encode message).length ≤ 2298 := by
  have bound_legOrdGrpComp := message.legOrdGrpComp.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length, CustOrderHandlingInst.encode_length, encodeMany_length_const LegOrdGrpComp.encode 8 LegOrdGrpComp.encode_length]
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
  rw [List.append_assoc, CustOrderHandlingInst.decode_encode, some_bind]
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

/-- New Order Complex Short Request: 122 bytes -/
structure NewOrderComplexShortRequest where
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
  marketSegmentId : BitVec 32
  matchInstCrossId : BitVec 32
  enrichmentRuleId : BitVec 16
  applSeqIndicator : BitVec 8
  selfMatchPreventionInstruction : BitVec 8
  productComplex : BitVec 8
  side : BitVec 8
  priceValidityCheckType : BitVec 8
  valueCheckTypeValue : BitVec 8
  orderAttributeLiquidityProvision : BitVec 8
  execInst : BitVec 8
  timeInForce : BitVec 8
  tradingCapacity : BitVec 8
  orderOrigination : BitVec 8
  partyIdInvestmentDecisionMakerQualifier : BitVec 8
  executingTraderQualifier : BitVec 8
  complianceText : Alpha 20
  pad5 : Alpha 5
  deriving DecidableEq, Repr

namespace NewOrderComplexShortRequest

def encode (message : NewOrderComplexShortRequest) : List UInt8 :=
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
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.matchInstCrossId
    ++ (encodeUIntLE 2 message.enrichmentRuleId
    ++ (encodeUInt 1 message.applSeqIndicator
    ++ (encodeUInt 1 message.selfMatchPreventionInstruction
    ++ (encodeUInt 1 message.productComplex
    ++ (encodeUInt 1 message.side
    ++ (encodeUInt 1 message.priceValidityCheckType
    ++ (encodeUInt 1 message.valueCheckTypeValue
    ++ (encodeUInt 1 message.orderAttributeLiquidityProvision
    ++ (encodeUInt 1 message.execInst
    ++ (encodeUInt 1 message.timeInForce
    ++ (encodeUInt 1 message.tradingCapacity
    ++ (encodeUInt 1 message.orderOrigination
    ++ (encodeUInt 1 message.partyIdInvestmentDecisionMakerQualifier
    ++ (encodeUInt 1 message.executingTraderQualifier
    ++ (Alpha.encode message.complianceText
    ++ (Alpha.encode message.pad5)))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (NewOrderComplexShortRequest × List UInt8) := do
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
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (matchInstCrossId, bytes) ← decodeUIntLE 4 bytes
  let (enrichmentRuleId, bytes) ← decodeUIntLE 2 bytes
  let (applSeqIndicator, bytes) ← decodeUInt 1 bytes
  let (selfMatchPreventionInstruction, bytes) ← decodeUInt 1 bytes
  let (productComplex, bytes) ← decodeUInt 1 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (priceValidityCheckType, bytes) ← decodeUInt 1 bytes
  let (valueCheckTypeValue, bytes) ← decodeUInt 1 bytes
  let (orderAttributeLiquidityProvision, bytes) ← decodeUInt 1 bytes
  let (execInst, bytes) ← decodeUInt 1 bytes
  let (timeInForce, bytes) ← decodeUInt 1 bytes
  let (tradingCapacity, bytes) ← decodeUInt 1 bytes
  let (orderOrigination, bytes) ← decodeUInt 1 bytes
  let (partyIdInvestmentDecisionMakerQualifier, bytes) ← decodeUInt 1 bytes
  let (executingTraderQualifier, bytes) ← decodeUInt 1 bytes
  let (complianceText, bytes) ← Alpha.decode 20 bytes
  let (pad5, bytes) ← Alpha.decode 5 bytes
  pure ({ networkMsgId, pad2, requestHeaderComp, securityId, price, orderQty, clOrdId, partyIdClientId, partyIdInvestmentDecisionMaker, executingTrader, marketSegmentId, matchInstCrossId, enrichmentRuleId, applSeqIndicator, selfMatchPreventionInstruction, productComplex, side, priceValidityCheckType, valueCheckTypeValue, orderAttributeLiquidityProvision, execInst, timeInForce, tradingCapacity, orderOrigination, partyIdInvestmentDecisionMakerQualifier, executingTraderQualifier, complianceText, pad5 }, bytes)

@[simp] theorem encode_length (message : NewOrderComplexShortRequest) : (encode message).length = 122 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : NewOrderComplexShortRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : NewOrderComplexShortRequest) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end NewOrderComplexShortRequest

/-- New Order Request -/
structure NewOrderRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  clOrdId : BitVec 64
  stopPx : BitVec 64
  partyIdClientId : BitVec 64
  executingTrader : BitVec 64
  matchInstCrossId : BitVec 32
  expireDate : BitVec 32
  tradingSessionSubId : BitVec 8
  selfMatchPreventionInstruction : BitVec 8
  applSeqIndicator : BitVec 8
  ordType : BitVec 8
  priceValidityCheckType : BitVec 8
  valueCheckTypeValue : BitVec 8
  orderOrigination : BitVec 8
  partyIdTakeUpTradingFirm : Alpha 5
  partyIdOrderOriginationFirm : Alpha 7
  partyIdBeneficiary : Alpha 9
  account : Alpha 2
  partyIdPositionAccount : Alpha 32
  positionEffect : PositionEffect
  partyIdLocationId : Alpha 2
  custOrderHandlingInst : CustOrderHandlingInst
  complianceText : Alpha 20
  freeText1 : Alpha 12
  freeText2 : Alpha 12
  freeText3 : Alpha 12
  fixClOrdId : Alpha 20
  partyEndClientIdentification : Alpha 20
  executingTraderQualifier : BitVec 8
  partyIdInvestmentDecisionMakerQualifier : BitVec 8
  orderAttributeRiskReduction : BitVec 8
  pad3 : Alpha 3
  partyIdInvestmentDecisionMaker : BitVec 64
  orderAttributeLiquidityProvision : BitVec 8
  tradingCapacity : BitVec 8
  productComplex : BitVec 8
  marketSegmentId : BitVec 32
  securityId : BitVec 64
  orderQty : BitVec 64
  price : BitVec 64
  side : BitVec 8
  execInst : BitVec 8
  timeInForce : BitVec 8
  pad1 : Alpha 1
  checkSumCorrection : BitVec 16
  pad2v2 : Alpha 2
  legOrdGrpComp : Bounded 1 LegOrdGrpComp
  deriving DecidableEq, Repr

namespace NewOrderRequest

def encode (message : NewOrderRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 8 message.stopPx
    ++ (encodeUIntLE 8 message.partyIdClientId
    ++ (encodeUIntLE 8 message.executingTrader
    ++ (encodeUIntLE 4 message.matchInstCrossId
    ++ (encodeUIntLE 4 message.expireDate
    ++ (encodeUInt 1 message.tradingSessionSubId
    ++ (encodeUInt 1 message.selfMatchPreventionInstruction
    ++ (encodeUInt 1 message.applSeqIndicator
    ++ (encodeUInt 1 message.ordType
    ++ (encodeUInt 1 message.priceValidityCheckType
    ++ (encodeUInt 1 message.valueCheckTypeValue
    ++ (encodeUInt 1 message.orderOrigination
    ++ (Alpha.encode message.partyIdTakeUpTradingFirm
    ++ (Alpha.encode message.partyIdOrderOriginationFirm
    ++ (Alpha.encode message.partyIdBeneficiary
    ++ (Alpha.encode message.account
    ++ (Alpha.encode message.partyIdPositionAccount
    ++ (PositionEffect.encode message.positionEffect
    ++ (Alpha.encode message.partyIdLocationId
    ++ (CustOrderHandlingInst.encode message.custOrderHandlingInst
    ++ (Alpha.encode message.complianceText
    ++ (Alpha.encode message.freeText1
    ++ (Alpha.encode message.freeText2
    ++ (Alpha.encode message.freeText3
    ++ (Alpha.encode message.fixClOrdId
    ++ (Alpha.encode message.partyEndClientIdentification
    ++ (encodeUInt 1 message.executingTraderQualifier
    ++ (encodeUInt 1 message.partyIdInvestmentDecisionMakerQualifier
    ++ (encodeUInt 1 message.orderAttributeRiskReduction
    ++ (Alpha.encode message.pad3
    ++ (encodeUIntLE 8 message.partyIdInvestmentDecisionMaker
    ++ (encodeUInt 1 message.orderAttributeLiquidityProvision
    ++ (encodeUInt 1 message.tradingCapacity
    ++ (encodeUInt 1 message.productComplex
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.legOrdGrpComp.val.length)
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.orderQty
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUInt 1 message.side
    ++ (encodeUInt 1 message.execInst
    ++ (encodeUInt 1 message.timeInForce
    ++ (Alpha.encode message.pad1
    ++ (encodeUIntLE 2 message.checkSumCorrection
    ++ (Alpha.encode message.pad2v2
    ++ (encodeMany LegOrdGrpComp.encode message.legOrdGrpComp.val)))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (NewOrderRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (stopPx, bytes) ← decodeUIntLE 8 bytes
  let (partyIdClientId, bytes) ← decodeUIntLE 8 bytes
  let (executingTrader, bytes) ← decodeUIntLE 8 bytes
  let (matchInstCrossId, bytes) ← decodeUIntLE 4 bytes
  let (expireDate, bytes) ← decodeUIntLE 4 bytes
  let (tradingSessionSubId, bytes) ← decodeUInt 1 bytes
  let (selfMatchPreventionInstruction, bytes) ← decodeUInt 1 bytes
  let (applSeqIndicator, bytes) ← decodeUInt 1 bytes
  let (ordType, bytes) ← decodeUInt 1 bytes
  let (priceValidityCheckType, bytes) ← decodeUInt 1 bytes
  let (valueCheckTypeValue, bytes) ← decodeUInt 1 bytes
  let (orderOrigination, bytes) ← decodeUInt 1 bytes
  let (partyIdTakeUpTradingFirm, bytes) ← Alpha.decode 5 bytes
  let (partyIdOrderOriginationFirm, bytes) ← Alpha.decode 7 bytes
  let (partyIdBeneficiary, bytes) ← Alpha.decode 9 bytes
  let (account, bytes) ← Alpha.decode 2 bytes
  let (partyIdPositionAccount, bytes) ← Alpha.decode 32 bytes
  let (positionEffect, bytes) ← PositionEffect.decode bytes
  let (partyIdLocationId, bytes) ← Alpha.decode 2 bytes
  let (custOrderHandlingInst, bytes) ← CustOrderHandlingInst.decode bytes
  let (complianceText, bytes) ← Alpha.decode 20 bytes
  let (freeText1, bytes) ← Alpha.decode 12 bytes
  let (freeText2, bytes) ← Alpha.decode 12 bytes
  let (freeText3, bytes) ← Alpha.decode 12 bytes
  let (fixClOrdId, bytes) ← Alpha.decode 20 bytes
  let (partyEndClientIdentification, bytes) ← Alpha.decode 20 bytes
  let (executingTraderQualifier, bytes) ← decodeUInt 1 bytes
  let (partyIdInvestmentDecisionMakerQualifier, bytes) ← decodeUInt 1 bytes
  let (orderAttributeRiskReduction, bytes) ← decodeUInt 1 bytes
  let (pad3, bytes) ← Alpha.decode 3 bytes
  let (partyIdInvestmentDecisionMaker, bytes) ← decodeUIntLE 8 bytes
  let (orderAttributeLiquidityProvision, bytes) ← decodeUInt 1 bytes
  let (tradingCapacity, bytes) ← decodeUInt 1 bytes
  let (productComplex, bytes) ← decodeUInt 1 bytes
  let (noLegOnbooks, bytes) ← decodeUInt 1 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (orderQty, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (execInst, bytes) ← decodeUInt 1 bytes
  let (timeInForce, bytes) ← decodeUInt 1 bytes
  let (pad1, bytes) ← Alpha.decode 1 bytes
  let (checkSumCorrection, bytes) ← decodeUIntLE 2 bytes
  let (pad2v2, bytes) ← Alpha.decode 2 bytes
  let (legOrdGrpComp_, bytes) ← decodeMany LegOrdGrpComp.decode noLegOnbooks.toNat bytes
  if fits_legOrdGrpComp : legOrdGrpComp_.length < 256 ^ 1 then
    pure ({ networkMsgId, pad2, requestHeaderComp, clOrdId, stopPx, partyIdClientId, executingTrader, matchInstCrossId, expireDate, tradingSessionSubId, selfMatchPreventionInstruction, applSeqIndicator, ordType, priceValidityCheckType, valueCheckTypeValue, orderOrigination, partyIdTakeUpTradingFirm, partyIdOrderOriginationFirm, partyIdBeneficiary, account, partyIdPositionAccount, positionEffect, partyIdLocationId, custOrderHandlingInst, complianceText, freeText1, freeText2, freeText3, fixClOrdId, partyEndClientIdentification, executingTraderQualifier, partyIdInvestmentDecisionMakerQualifier, orderAttributeRiskReduction, pad3, partyIdInvestmentDecisionMaker, orderAttributeLiquidityProvision, tradingCapacity, productComplex, marketSegmentId, securityId, orderQty, price, side, execInst, timeInForce, pad1, checkSumCorrection, pad2v2, legOrdGrpComp := ⟨legOrdGrpComp_, fits_legOrdGrpComp⟩ }, bytes)
  else none

theorem encode_length_pos (message : NewOrderRequest) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : NewOrderRequest) : (encode message).length ≤ 2314 := by
  have bound_legOrdGrpComp := message.legOrdGrpComp.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length, PositionEffect.encode_length, CustOrderHandlingInst.encode_length, encodeMany_length_const LegOrdGrpComp.encode 8 LegOrdGrpComp.encode_length]
  omega

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : NewOrderRequest) (rest : List UInt8) :
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
  rw [List.append_assoc, PositionEffect.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CustOrderHandlingInst.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 LegOrdGrpComp.encode LegOrdGrpComp.decode LegOrdGrpComp.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.legOrdGrpComp.length_lt]
  rfl

end NewOrderRequest

/-- New Order Short Request: 130 bytes -/
structure NewOrderShortRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  clOrdId : BitVec 64
  partyIdClientId : BitVec 64
  executingTrader : BitVec 64
  matchInstCrossId : BitVec 32
  applSeqIndicator : BitVec 8
  priceValidityCheckType : BitVec 8
  valueCheckTypeValue : BitVec 8
  tradingCapacity : BitVec 8
  orderOrigination : BitVec 8
  executingTraderQualifier : BitVec 8
  partyIdInvestmentDecisionMakerQualifier : BitVec 8
  complianceText : Alpha 20
  pad1v2 : Alpha 1
  partyIdInvestmentDecisionMaker : BitVec 64
  enrichmentRuleId : BitVec 16
  orderAttributeLiquidityProvision : BitVec 8
  productComplex : BitVec 8
  selfMatchPreventionInstruction : BitVec 8
  pad3 : Alpha 3
  marketSegmentId : BitVec 32
  pad4v1 : Alpha 4
  securityId : BitVec 64
  orderQty : BitVec 64
  price : BitVec 64
  side : BitVec 8
  execInst : BitVec 8
  timeInForce : BitVec 8
  pad1v1 : Alpha 1
  checkSumCorrection : BitVec 16
  pad2v2 : Alpha 2
  deriving DecidableEq, Repr

namespace NewOrderShortRequest

def encode (message : NewOrderShortRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 8 message.partyIdClientId
    ++ (encodeUIntLE 8 message.executingTrader
    ++ (encodeUIntLE 4 message.matchInstCrossId
    ++ (encodeUInt 1 message.applSeqIndicator
    ++ (encodeUInt 1 message.priceValidityCheckType
    ++ (encodeUInt 1 message.valueCheckTypeValue
    ++ (encodeUInt 1 message.tradingCapacity
    ++ (encodeUInt 1 message.orderOrigination
    ++ (encodeUInt 1 message.executingTraderQualifier
    ++ (encodeUInt 1 message.partyIdInvestmentDecisionMakerQualifier
    ++ (Alpha.encode message.complianceText
    ++ (Alpha.encode message.pad1v2
    ++ (encodeUIntLE 8 message.partyIdInvestmentDecisionMaker
    ++ (encodeUIntLE 2 message.enrichmentRuleId
    ++ (encodeUInt 1 message.orderAttributeLiquidityProvision
    ++ (encodeUInt 1 message.productComplex
    ++ (encodeUInt 1 message.selfMatchPreventionInstruction
    ++ (Alpha.encode message.pad3
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (Alpha.encode message.pad4v1
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.orderQty
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUInt 1 message.side
    ++ (encodeUInt 1 message.execInst
    ++ (encodeUInt 1 message.timeInForce
    ++ (Alpha.encode message.pad1v1
    ++ (encodeUIntLE 2 message.checkSumCorrection
    ++ (Alpha.encode message.pad2v2))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (NewOrderShortRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (partyIdClientId, bytes) ← decodeUIntLE 8 bytes
  let (executingTrader, bytes) ← decodeUIntLE 8 bytes
  let (matchInstCrossId, bytes) ← decodeUIntLE 4 bytes
  let (applSeqIndicator, bytes) ← decodeUInt 1 bytes
  let (priceValidityCheckType, bytes) ← decodeUInt 1 bytes
  let (valueCheckTypeValue, bytes) ← decodeUInt 1 bytes
  let (tradingCapacity, bytes) ← decodeUInt 1 bytes
  let (orderOrigination, bytes) ← decodeUInt 1 bytes
  let (executingTraderQualifier, bytes) ← decodeUInt 1 bytes
  let (partyIdInvestmentDecisionMakerQualifier, bytes) ← decodeUInt 1 bytes
  let (complianceText, bytes) ← Alpha.decode 20 bytes
  let (pad1v2, bytes) ← Alpha.decode 1 bytes
  let (partyIdInvestmentDecisionMaker, bytes) ← decodeUIntLE 8 bytes
  let (enrichmentRuleId, bytes) ← decodeUIntLE 2 bytes
  let (orderAttributeLiquidityProvision, bytes) ← decodeUInt 1 bytes
  let (productComplex, bytes) ← decodeUInt 1 bytes
  let (selfMatchPreventionInstruction, bytes) ← decodeUInt 1 bytes
  let (pad3, bytes) ← Alpha.decode 3 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (pad4v1, bytes) ← Alpha.decode 4 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (orderQty, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (execInst, bytes) ← decodeUInt 1 bytes
  let (timeInForce, bytes) ← decodeUInt 1 bytes
  let (pad1v1, bytes) ← Alpha.decode 1 bytes
  let (checkSumCorrection, bytes) ← decodeUIntLE 2 bytes
  let (pad2v2, bytes) ← Alpha.decode 2 bytes
  pure ({ networkMsgId, pad2, requestHeaderComp, clOrdId, partyIdClientId, executingTrader, matchInstCrossId, applSeqIndicator, priceValidityCheckType, valueCheckTypeValue, tradingCapacity, orderOrigination, executingTraderQualifier, partyIdInvestmentDecisionMakerQualifier, complianceText, pad1v2, partyIdInvestmentDecisionMaker, enrichmentRuleId, orderAttributeLiquidityProvision, productComplex, selfMatchPreventionInstruction, pad3, marketSegmentId, pad4v1, securityId, orderQty, price, side, execInst, timeInForce, pad1v1, checkSumCorrection, pad2v2 }, bytes)

@[simp] theorem encode_length (message : NewOrderShortRequest) : (encode message).length = 130 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : NewOrderShortRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : NewOrderShortRequest) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end NewOrderShortRequest

/-- New Order Single Request: 266 bytes -/
structure NewOrderSingleRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  price : BitVec 64
  orderQty : BitVec 64
  stopPx : BitVec 64
  clOrdId : BitVec 64
  securityId : BitVec 64
  partyIdClientId : BitVec 64
  partyIdInvestmentDecisionMaker : BitVec 64
  executingTrader : BitVec 64
  expireDate : BitVec 32
  marketSegmentId : BitVec 32
  matchInstCrossId : BitVec 32
  selfMatchPreventionInstruction : BitVec 8
  partyIdTakeUpTradingFirm : Alpha 5
  partyIdOrderOriginationFirm : Alpha 7
  partyIdBeneficiary : Alpha 9
  applSeqIndicator : BitVec 8
  productComplex : BitVec 8
  side : BitVec 8
  ordType : BitVec 8
  priceValidityCheckType : BitVec 8
  valueCheckTypeValue : BitVec 8
  orderAttributeLiquidityProvision : BitVec 8
  orderAttributeRiskReduction : BitVec 8
  timeInForce : BitVec 8
  execInst : BitVec 8
  tradingSessionSubId : BitVec 8
  tradingCapacity : BitVec 8
  orderOrigination : BitVec 8
  partyIdInvestmentDecisionMakerQualifier : BitVec 8
  executingTraderQualifier : BitVec 8
  account : Alpha 2
  partyIdPositionAccount : Alpha 32
  positionEffect : PositionEffect
  partyIdLocationId : Alpha 2
  custOrderHandlingInst : CustOrderHandlingInst
  complianceText : Alpha 20
  freeText1 : Alpha 12
  freeText2 : Alpha 12
  freeText3 : Alpha 12
  fixClOrdId : Alpha 20
  partyEndClientIdentification : Alpha 20
  pad1 : Alpha 1
  deriving DecidableEq, Repr

namespace NewOrderSingleRequest

def encode (message : NewOrderSingleRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 8 message.orderQty
    ++ (encodeUIntLE 8 message.stopPx
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.partyIdClientId
    ++ (encodeUIntLE 8 message.partyIdInvestmentDecisionMaker
    ++ (encodeUIntLE 8 message.executingTrader
    ++ (encodeUIntLE 4 message.expireDate
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.matchInstCrossId
    ++ (encodeUInt 1 message.selfMatchPreventionInstruction
    ++ (Alpha.encode message.partyIdTakeUpTradingFirm
    ++ (Alpha.encode message.partyIdOrderOriginationFirm
    ++ (Alpha.encode message.partyIdBeneficiary
    ++ (encodeUInt 1 message.applSeqIndicator
    ++ (encodeUInt 1 message.productComplex
    ++ (encodeUInt 1 message.side
    ++ (encodeUInt 1 message.ordType
    ++ (encodeUInt 1 message.priceValidityCheckType
    ++ (encodeUInt 1 message.valueCheckTypeValue
    ++ (encodeUInt 1 message.orderAttributeLiquidityProvision
    ++ (encodeUInt 1 message.orderAttributeRiskReduction
    ++ (encodeUInt 1 message.timeInForce
    ++ (encodeUInt 1 message.execInst
    ++ (encodeUInt 1 message.tradingSessionSubId
    ++ (encodeUInt 1 message.tradingCapacity
    ++ (encodeUInt 1 message.orderOrigination
    ++ (encodeUInt 1 message.partyIdInvestmentDecisionMakerQualifier
    ++ (encodeUInt 1 message.executingTraderQualifier
    ++ (Alpha.encode message.account
    ++ (Alpha.encode message.partyIdPositionAccount
    ++ (PositionEffect.encode message.positionEffect
    ++ (Alpha.encode message.partyIdLocationId
    ++ (CustOrderHandlingInst.encode message.custOrderHandlingInst
    ++ (Alpha.encode message.complianceText
    ++ (Alpha.encode message.freeText1
    ++ (Alpha.encode message.freeText2
    ++ (Alpha.encode message.freeText3
    ++ (Alpha.encode message.fixClOrdId
    ++ (Alpha.encode message.partyEndClientIdentification
    ++ (Alpha.encode message.pad1))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (NewOrderSingleRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (orderQty, bytes) ← decodeUIntLE 8 bytes
  let (stopPx, bytes) ← decodeUIntLE 8 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (partyIdClientId, bytes) ← decodeUIntLE 8 bytes
  let (partyIdInvestmentDecisionMaker, bytes) ← decodeUIntLE 8 bytes
  let (executingTrader, bytes) ← decodeUIntLE 8 bytes
  let (expireDate, bytes) ← decodeUIntLE 4 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (matchInstCrossId, bytes) ← decodeUIntLE 4 bytes
  let (selfMatchPreventionInstruction, bytes) ← decodeUInt 1 bytes
  let (partyIdTakeUpTradingFirm, bytes) ← Alpha.decode 5 bytes
  let (partyIdOrderOriginationFirm, bytes) ← Alpha.decode 7 bytes
  let (partyIdBeneficiary, bytes) ← Alpha.decode 9 bytes
  let (applSeqIndicator, bytes) ← decodeUInt 1 bytes
  let (productComplex, bytes) ← decodeUInt 1 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (ordType, bytes) ← decodeUInt 1 bytes
  let (priceValidityCheckType, bytes) ← decodeUInt 1 bytes
  let (valueCheckTypeValue, bytes) ← decodeUInt 1 bytes
  let (orderAttributeLiquidityProvision, bytes) ← decodeUInt 1 bytes
  let (orderAttributeRiskReduction, bytes) ← decodeUInt 1 bytes
  let (timeInForce, bytes) ← decodeUInt 1 bytes
  let (execInst, bytes) ← decodeUInt 1 bytes
  let (tradingSessionSubId, bytes) ← decodeUInt 1 bytes
  let (tradingCapacity, bytes) ← decodeUInt 1 bytes
  let (orderOrigination, bytes) ← decodeUInt 1 bytes
  let (partyIdInvestmentDecisionMakerQualifier, bytes) ← decodeUInt 1 bytes
  let (executingTraderQualifier, bytes) ← decodeUInt 1 bytes
  let (account, bytes) ← Alpha.decode 2 bytes
  let (partyIdPositionAccount, bytes) ← Alpha.decode 32 bytes
  let (positionEffect, bytes) ← PositionEffect.decode bytes
  let (partyIdLocationId, bytes) ← Alpha.decode 2 bytes
  let (custOrderHandlingInst, bytes) ← CustOrderHandlingInst.decode bytes
  let (complianceText, bytes) ← Alpha.decode 20 bytes
  let (freeText1, bytes) ← Alpha.decode 12 bytes
  let (freeText2, bytes) ← Alpha.decode 12 bytes
  let (freeText3, bytes) ← Alpha.decode 12 bytes
  let (fixClOrdId, bytes) ← Alpha.decode 20 bytes
  let (partyEndClientIdentification, bytes) ← Alpha.decode 20 bytes
  let (pad1, bytes) ← Alpha.decode 1 bytes
  pure ({ networkMsgId, pad2, requestHeaderComp, price, orderQty, stopPx, clOrdId, securityId, partyIdClientId, partyIdInvestmentDecisionMaker, executingTrader, expireDate, marketSegmentId, matchInstCrossId, selfMatchPreventionInstruction, partyIdTakeUpTradingFirm, partyIdOrderOriginationFirm, partyIdBeneficiary, applSeqIndicator, productComplex, side, ordType, priceValidityCheckType, valueCheckTypeValue, orderAttributeLiquidityProvision, orderAttributeRiskReduction, timeInForce, execInst, tradingSessionSubId, tradingCapacity, orderOrigination, partyIdInvestmentDecisionMakerQualifier, executingTraderQualifier, account, partyIdPositionAccount, positionEffect, partyIdLocationId, custOrderHandlingInst, complianceText, freeText1, freeText2, freeText3, fixClOrdId, partyEndClientIdentification, pad1 }, bytes)

@[simp] theorem encode_length (message : NewOrderSingleRequest) : (encode message).length = 266 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length, PositionEffect.encode_length, CustOrderHandlingInst.encode_length]

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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, PositionEffect.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CustOrderHandlingInst.decode_encode, some_bind]
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

/-- New Order Single Short Request: 114 bytes -/
structure NewOrderSingleShortRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  price : BitVec 64
  orderQty : BitVec 64
  clOrdId : BitVec 64
  partyIdClientId : BitVec 64
  partyIdInvestmentDecisionMaker : BitVec 64
  executingTrader : BitVec 64
  simpleSecurityId : BitVec 32
  matchInstCrossId : BitVec 32
  enrichmentRuleId : BitVec 16
  selfMatchPreventionInstruction : BitVec 8
  side : BitVec 8
  applSeqIndicator : BitVec 8
  priceValidityCheckType : BitVec 8
  valueCheckTypeValue : BitVec 8
  orderAttributeLiquidityProvision : BitVec 8
  timeInForce : BitVec 8
  execInst : BitVec 8
  tradingCapacity : BitVec 8
  orderOrigination : BitVec 8
  partyIdInvestmentDecisionMakerQualifier : BitVec 8
  executingTraderQualifier : BitVec 8
  complianceText : Alpha 20
  pad6 : Alpha 6
  deriving DecidableEq, Repr

namespace NewOrderSingleShortRequest

def encode (message : NewOrderSingleShortRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 8 message.orderQty
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 8 message.partyIdClientId
    ++ (encodeUIntLE 8 message.partyIdInvestmentDecisionMaker
    ++ (encodeUIntLE 8 message.executingTrader
    ++ (encodeUIntLE 4 message.simpleSecurityId
    ++ (encodeUIntLE 4 message.matchInstCrossId
    ++ (encodeUIntLE 2 message.enrichmentRuleId
    ++ (encodeUInt 1 message.selfMatchPreventionInstruction
    ++ (encodeUInt 1 message.side
    ++ (encodeUInt 1 message.applSeqIndicator
    ++ (encodeUInt 1 message.priceValidityCheckType
    ++ (encodeUInt 1 message.valueCheckTypeValue
    ++ (encodeUInt 1 message.orderAttributeLiquidityProvision
    ++ (encodeUInt 1 message.timeInForce
    ++ (encodeUInt 1 message.execInst
    ++ (encodeUInt 1 message.tradingCapacity
    ++ (encodeUInt 1 message.orderOrigination
    ++ (encodeUInt 1 message.partyIdInvestmentDecisionMakerQualifier
    ++ (encodeUInt 1 message.executingTraderQualifier
    ++ (Alpha.encode message.complianceText
    ++ (Alpha.encode message.pad6)))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (NewOrderSingleShortRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (orderQty, bytes) ← decodeUIntLE 8 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (partyIdClientId, bytes) ← decodeUIntLE 8 bytes
  let (partyIdInvestmentDecisionMaker, bytes) ← decodeUIntLE 8 bytes
  let (executingTrader, bytes) ← decodeUIntLE 8 bytes
  let (simpleSecurityId, bytes) ← decodeUIntLE 4 bytes
  let (matchInstCrossId, bytes) ← decodeUIntLE 4 bytes
  let (enrichmentRuleId, bytes) ← decodeUIntLE 2 bytes
  let (selfMatchPreventionInstruction, bytes) ← decodeUInt 1 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (applSeqIndicator, bytes) ← decodeUInt 1 bytes
  let (priceValidityCheckType, bytes) ← decodeUInt 1 bytes
  let (valueCheckTypeValue, bytes) ← decodeUInt 1 bytes
  let (orderAttributeLiquidityProvision, bytes) ← decodeUInt 1 bytes
  let (timeInForce, bytes) ← decodeUInt 1 bytes
  let (execInst, bytes) ← decodeUInt 1 bytes
  let (tradingCapacity, bytes) ← decodeUInt 1 bytes
  let (orderOrigination, bytes) ← decodeUInt 1 bytes
  let (partyIdInvestmentDecisionMakerQualifier, bytes) ← decodeUInt 1 bytes
  let (executingTraderQualifier, bytes) ← decodeUInt 1 bytes
  let (complianceText, bytes) ← Alpha.decode 20 bytes
  let (pad6, bytes) ← Alpha.decode 6 bytes
  pure ({ networkMsgId, pad2, requestHeaderComp, price, orderQty, clOrdId, partyIdClientId, partyIdInvestmentDecisionMaker, executingTrader, simpleSecurityId, matchInstCrossId, enrichmentRuleId, selfMatchPreventionInstruction, side, applSeqIndicator, priceValidityCheckType, valueCheckTypeValue, orderAttributeLiquidityProvision, timeInForce, execInst, tradingCapacity, orderOrigination, partyIdInvestmentDecisionMakerQualifier, executingTraderQualifier, complianceText, pad6 }, bytes)

@[simp] theorem encode_length (message : NewOrderSingleShortRequest) : (encode message).length = 114 := by
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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

/-- Risk Limit Qty Grp Comp: 16 bytes -/
structure RiskLimitQtyGrpComp where
  riskLimitQty : BitVec 64
  riskLimitType : BitVec 8
  pad7 : Alpha 7
  deriving DecidableEq, Repr

namespace RiskLimitQtyGrpComp

def encode (message : RiskLimitQtyGrpComp) : List UInt8 :=
  encodeUIntLE 8 message.riskLimitQty
    ++ (encodeUInt 1 message.riskLimitType
    ++ (Alpha.encode message.pad7))

def decode (bytes : List UInt8) : Option (RiskLimitQtyGrpComp × List UInt8) := do
  let (riskLimitQty, bytes) ← decodeUIntLE 8 bytes
  let (riskLimitType, bytes) ← decodeUInt 1 bytes
  let (pad7, bytes) ← Alpha.decode 7 bytes
  pure ({ riskLimitQty, riskLimitType, pad7 }, bytes)

@[simp] theorem encode_length (message : RiskLimitQtyGrpComp) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : RiskLimitQtyGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RiskLimitQtyGrpComp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end RiskLimitQtyGrpComp

/-- Pre Trade Risk Limits Definition Request -/
structure PreTradeRiskLimitsDefinitionRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  nettingCoefficient : BitVec 64
  quoteWeightingCoefficient : BitVec 64
  marketSegmentId : BitVec 32
  riskLimitPlatform : BitVec 8
  partyDetailStatus : BitVec 8
  riskLimitGroup : Alpha 3
  partyDetailExecutingUnit : Alpha 5
  pad1 : Alpha 1
  riskLimitQtyGrpComp : Bounded 1 RiskLimitQtyGrpComp
  deriving DecidableEq, Repr

namespace PreTradeRiskLimitsDefinitionRequest

def encode (message : PreTradeRiskLimitsDefinitionRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 8 message.nettingCoefficient
    ++ (encodeUIntLE 8 message.quoteWeightingCoefficient
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUInt 1 message.riskLimitPlatform
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.riskLimitQtyGrpComp.val.length)
    ++ (encodeUInt 1 message.partyDetailStatus
    ++ (Alpha.encode message.riskLimitGroup
    ++ (Alpha.encode message.partyDetailExecutingUnit
    ++ (Alpha.encode message.pad1
    ++ (encodeMany RiskLimitQtyGrpComp.encode message.riskLimitQtyGrpComp.val))))))))))))

def decode (bytes : List UInt8) : Option (PreTradeRiskLimitsDefinitionRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (nettingCoefficient, bytes) ← decodeUIntLE 8 bytes
  let (quoteWeightingCoefficient, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (riskLimitPlatform, bytes) ← decodeUInt 1 bytes
  let (noRiskLimitsQty, bytes) ← decodeUInt 1 bytes
  let (partyDetailStatus, bytes) ← decodeUInt 1 bytes
  let (riskLimitGroup, bytes) ← Alpha.decode 3 bytes
  let (partyDetailExecutingUnit, bytes) ← Alpha.decode 5 bytes
  let (pad1, bytes) ← Alpha.decode 1 bytes
  let (riskLimitQtyGrpComp_, bytes) ← decodeMany RiskLimitQtyGrpComp.decode noRiskLimitsQty.toNat bytes
  if fits_riskLimitQtyGrpComp : riskLimitQtyGrpComp_.length < 256 ^ 1 then
    pure ({ networkMsgId, pad2, requestHeaderComp, nettingCoefficient, quoteWeightingCoefficient, marketSegmentId, riskLimitPlatform, partyDetailStatus, riskLimitGroup, partyDetailExecutingUnit, pad1, riskLimitQtyGrpComp := ⟨riskLimitQtyGrpComp_, fits_riskLimitQtyGrpComp⟩ }, bytes)
  else none

theorem encode_length_pos (message : PreTradeRiskLimitsDefinitionRequest) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : PreTradeRiskLimitsDefinitionRequest) : (encode message).length ≤ 4130 := by
  have bound_riskLimitQtyGrpComp := message.riskLimitQtyGrpComp.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const RiskLimitQtyGrpComp.encode 16 RiskLimitQtyGrpComp.encode_length]
  omega

@[simp] theorem decode_encode (message : PreTradeRiskLimitsDefinitionRequest) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 RiskLimitQtyGrpComp.encode RiskLimitQtyGrpComp.decode RiskLimitQtyGrpComp.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.riskLimitQtyGrpComp.length_lt]
  rfl

end PreTradeRiskLimitsDefinitionRequest

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
  massActionSubType : BitVec 8
  partyIdInvestmentDecisionMakerQualifier : BitVec 8
  executingTraderQualifier : BitVec 8
  pad4 : Alpha 4
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
    ++ (encodeUInt 1 message.massActionSubType
    ++ (encodeUInt 1 message.partyIdInvestmentDecisionMakerQualifier
    ++ (encodeUInt 1 message.executingTraderQualifier
    ++ (Alpha.encode message.pad4)))))))))))

def decode (bytes : List UInt8) : Option (QuoteActivationRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (partyIdInvestmentDecisionMaker, bytes) ← decodeUIntLE 8 bytes
  let (executingTrader, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (targetPartyIdSessionId, bytes) ← decodeUIntLE 4 bytes
  let (massActionType, bytes) ← decodeUInt 1 bytes
  let (massActionSubType, bytes) ← decodeUInt 1 bytes
  let (partyIdInvestmentDecisionMakerQualifier, bytes) ← decodeUInt 1 bytes
  let (executingTraderQualifier, bytes) ← decodeUInt 1 bytes
  let (pad4, bytes) ← Alpha.decode 4 bytes
  pure ({ networkMsgId, pad2, requestHeaderComp, partyIdInvestmentDecisionMaker, executingTrader, marketSegmentId, targetPartyIdSessionId, massActionType, massActionSubType, partyIdInvestmentDecisionMakerQualifier, executingTraderQualifier, pad4 }, bytes)

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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end QuoteActivationRequest

/-- Rfq Request: 66 bytes -/
structure RfqRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  securityId : BitVec 64
  orderQty : BitVec 64
  marketSegmentId : BitVec 32
  side : BitVec 8
  complianceText : Alpha 20
  pad7 : Alpha 7
  deriving DecidableEq, Repr

namespace RfqRequest

def encode (message : RfqRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.orderQty
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUInt 1 message.side
    ++ (Alpha.encode message.complianceText
    ++ (Alpha.encode message.pad7))))))))

def decode (bytes : List UInt8) : Option (RfqRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (orderQty, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (complianceText, bytes) ← Alpha.decode 20 bytes
  let (pad7, bytes) ← Alpha.decode 7 bytes
  pure ({ networkMsgId, pad2, requestHeaderComp, securityId, orderQty, marketSegmentId, side, complianceText, pad7 }, bytes)

@[simp] theorem encode_length (message : RfqRequest) : (encode message).length = 66 := by
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
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

/-- Reverse Tes Trade Request: 194 bytes -/
structure ReverseTesTradeRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  marketSegmentId : BitVec 32
  packageId : BitVec 32
  tesExecId : BitVec 32
  relatedMarketSegmentId : BitVec 32
  trdType : BitVec 16
  tradeReportId : Alpha 20
  reversalReasonText : Alpha 132
  pad6 : Alpha 6
  deriving DecidableEq, Repr

namespace ReverseTesTradeRequest

def encode (message : ReverseTesTradeRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.packageId
    ++ (encodeUIntLE 4 message.tesExecId
    ++ (encodeUIntLE 4 message.relatedMarketSegmentId
    ++ (encodeUIntLE 2 message.trdType
    ++ (Alpha.encode message.tradeReportId
    ++ (Alpha.encode message.reversalReasonText
    ++ (Alpha.encode message.pad6))))))))))

def decode (bytes : List UInt8) : Option (ReverseTesTradeRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (packageId, bytes) ← decodeUIntLE 4 bytes
  let (tesExecId, bytes) ← decodeUIntLE 4 bytes
  let (relatedMarketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (trdType, bytes) ← decodeUIntLE 2 bytes
  let (tradeReportId, bytes) ← Alpha.decode 20 bytes
  let (reversalReasonText, bytes) ← Alpha.decode 132 bytes
  let (pad6, bytes) ← Alpha.decode 6 bytes
  pure ({ networkMsgId, pad2, requestHeaderComp, marketSegmentId, packageId, tesExecId, relatedMarketSegmentId, trdType, tradeReportId, reversalReasonText, pad6 }, bytes)

@[simp] theorem encode_length (message : ReverseTesTradeRequest) : (encode message).length = 194 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : ReverseTesTradeRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ReverseTesTradeRequest) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end ReverseTesTradeRequest

/-- Srqs Enter Quote Request: 370 bytes -/
structure SrqsEnterQuoteRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  bidPx : BitVec 64
  offerPx : BitVec 64
  underlyingDeltaPercentage : BitVec 64
  bidSize : BitVec 64
  offerSize : BitVec 64
  partyIdClientId : BitVec 64
  partyIdInvestmentDecisionMaker : BitVec 64
  executingTrader : BitVec 64
  quoteRefPrice : BitVec 64
  validUntilTime : BitVec 64
  marketSegmentId : BitVec 32
  negotiationId : BitVec 32
  orderAttributeLiquidityProvision : BitVec 8
  executingTraderQualifier : BitVec 8
  partyIdInvestmentDecisionMakerQualifier : BitVec 8
  tradingCapacity : BitVec 8
  partyExecutingFirm : Alpha 5
  partyExecutingTrader : Alpha 6
  freeText1 : Alpha 12
  freeText2 : Alpha 12
  freeText3 : Alpha 12
  freeText5 : Alpha 132
  positionEffect : PositionEffect
  account : Alpha 2
  partyIdBeneficiary : Alpha 9
  custOrderHandlingInst : CustOrderHandlingInst
  partyIdOrderOriginationFirm : Alpha 7
  partyIdPositionAccount : Alpha 32
  partyIdLocationId : Alpha 2
  complianceText : Alpha 20
  partyIdTakeUpTradingFirm : Alpha 5
  pad2v2 : Alpha 2
  deriving DecidableEq, Repr

namespace SrqsEnterQuoteRequest

def encode (message : SrqsEnterQuoteRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 8 message.bidPx
    ++ (encodeUIntLE 8 message.offerPx
    ++ (encodeUIntLE 8 message.underlyingDeltaPercentage
    ++ (encodeUIntLE 8 message.bidSize
    ++ (encodeUIntLE 8 message.offerSize
    ++ (encodeUIntLE 8 message.partyIdClientId
    ++ (encodeUIntLE 8 message.partyIdInvestmentDecisionMaker
    ++ (encodeUIntLE 8 message.executingTrader
    ++ (encodeUIntLE 8 message.quoteRefPrice
    ++ (encodeUIntLE 8 message.validUntilTime
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.negotiationId
    ++ (encodeUInt 1 message.orderAttributeLiquidityProvision
    ++ (encodeUInt 1 message.executingTraderQualifier
    ++ (encodeUInt 1 message.partyIdInvestmentDecisionMakerQualifier
    ++ (encodeUInt 1 message.tradingCapacity
    ++ (Alpha.encode message.partyExecutingFirm
    ++ (Alpha.encode message.partyExecutingTrader
    ++ (Alpha.encode message.freeText1
    ++ (Alpha.encode message.freeText2
    ++ (Alpha.encode message.freeText3
    ++ (Alpha.encode message.freeText5
    ++ (PositionEffect.encode message.positionEffect
    ++ (Alpha.encode message.account
    ++ (Alpha.encode message.partyIdBeneficiary
    ++ (CustOrderHandlingInst.encode message.custOrderHandlingInst
    ++ (Alpha.encode message.partyIdOrderOriginationFirm
    ++ (Alpha.encode message.partyIdPositionAccount
    ++ (Alpha.encode message.partyIdLocationId
    ++ (Alpha.encode message.complianceText
    ++ (Alpha.encode message.partyIdTakeUpTradingFirm
    ++ (Alpha.encode message.pad2v2))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (SrqsEnterQuoteRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (bidPx, bytes) ← decodeUIntLE 8 bytes
  let (offerPx, bytes) ← decodeUIntLE 8 bytes
  let (underlyingDeltaPercentage, bytes) ← decodeUIntLE 8 bytes
  let (bidSize, bytes) ← decodeUIntLE 8 bytes
  let (offerSize, bytes) ← decodeUIntLE 8 bytes
  let (partyIdClientId, bytes) ← decodeUIntLE 8 bytes
  let (partyIdInvestmentDecisionMaker, bytes) ← decodeUIntLE 8 bytes
  let (executingTrader, bytes) ← decodeUIntLE 8 bytes
  let (quoteRefPrice, bytes) ← decodeUIntLE 8 bytes
  let (validUntilTime, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (negotiationId, bytes) ← decodeUIntLE 4 bytes
  let (orderAttributeLiquidityProvision, bytes) ← decodeUInt 1 bytes
  let (executingTraderQualifier, bytes) ← decodeUInt 1 bytes
  let (partyIdInvestmentDecisionMakerQualifier, bytes) ← decodeUInt 1 bytes
  let (tradingCapacity, bytes) ← decodeUInt 1 bytes
  let (partyExecutingFirm, bytes) ← Alpha.decode 5 bytes
  let (partyExecutingTrader, bytes) ← Alpha.decode 6 bytes
  let (freeText1, bytes) ← Alpha.decode 12 bytes
  let (freeText2, bytes) ← Alpha.decode 12 bytes
  let (freeText3, bytes) ← Alpha.decode 12 bytes
  let (freeText5, bytes) ← Alpha.decode 132 bytes
  let (positionEffect, bytes) ← PositionEffect.decode bytes
  let (account, bytes) ← Alpha.decode 2 bytes
  let (partyIdBeneficiary, bytes) ← Alpha.decode 9 bytes
  let (custOrderHandlingInst, bytes) ← CustOrderHandlingInst.decode bytes
  let (partyIdOrderOriginationFirm, bytes) ← Alpha.decode 7 bytes
  let (partyIdPositionAccount, bytes) ← Alpha.decode 32 bytes
  let (partyIdLocationId, bytes) ← Alpha.decode 2 bytes
  let (complianceText, bytes) ← Alpha.decode 20 bytes
  let (partyIdTakeUpTradingFirm, bytes) ← Alpha.decode 5 bytes
  let (pad2v2, bytes) ← Alpha.decode 2 bytes
  pure ({ networkMsgId, pad2, requestHeaderComp, bidPx, offerPx, underlyingDeltaPercentage, bidSize, offerSize, partyIdClientId, partyIdInvestmentDecisionMaker, executingTrader, quoteRefPrice, validUntilTime, marketSegmentId, negotiationId, orderAttributeLiquidityProvision, executingTraderQualifier, partyIdInvestmentDecisionMakerQualifier, tradingCapacity, partyExecutingFirm, partyExecutingTrader, freeText1, freeText2, freeText3, freeText5, positionEffect, account, partyIdBeneficiary, custOrderHandlingInst, partyIdOrderOriginationFirm, partyIdPositionAccount, partyIdLocationId, complianceText, partyIdTakeUpTradingFirm, pad2v2 }, bytes)

@[simp] theorem encode_length (message : SrqsEnterQuoteRequest) : (encode message).length = 370 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length, PositionEffect.encode_length, CustOrderHandlingInst.encode_length]

theorem encode_length_pos (message : SrqsEnterQuoteRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : SrqsEnterQuoteRequest) (rest : List UInt8) :
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
  rw [List.append_assoc, PositionEffect.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CustOrderHandlingInst.decode_encode, some_bind]
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

end SrqsEnterQuoteRequest

/-- Srqs Hit Quote Grp Comp: 24 bytes -/
structure SrqsHitQuoteGrpComp where
  orderQty : BitVec 64
  quoteId : BitVec 64
  side : BitVec 8
  pad7 : Alpha 7
  deriving DecidableEq, Repr

namespace SrqsHitQuoteGrpComp

def encode (message : SrqsHitQuoteGrpComp) : List UInt8 :=
  encodeUIntLE 8 message.orderQty
    ++ (encodeUIntLE 8 message.quoteId
    ++ (encodeUInt 1 message.side
    ++ (Alpha.encode message.pad7)))

def decode (bytes : List UInt8) : Option (SrqsHitQuoteGrpComp × List UInt8) := do
  let (orderQty, bytes) ← decodeUIntLE 8 bytes
  let (quoteId, bytes) ← decodeUIntLE 8 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (pad7, bytes) ← Alpha.decode 7 bytes
  pure ({ orderQty, quoteId, side, pad7 }, bytes)

@[simp] theorem encode_length (message : SrqsHitQuoteGrpComp) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : SrqsHitQuoteGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SrqsHitQuoteGrpComp) (rest : List UInt8) :
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

end SrqsHitQuoteGrpComp

/-- Srqs Hit Quote Request -/
structure SrqsHitQuoteRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  validUntilTime : BitVec 64
  underlyingQty : BitVec 64
  underlyingPriceStipValue : BitVec 64
  partyIdClientId : BitVec 64
  partyIdInvestmentDecisionMaker : BitVec 64
  executingTrader : BitVec 64
  marketSegmentId : BitVec 32
  negotiationId : BitVec 32
  orderAttributeLiquidityProvision : BitVec 8
  executingTraderQualifier : BitVec 8
  partyIdInvestmentDecisionMakerQualifier : BitVec 8
  tradingCapacity : BitVec 8
  tradePublishIndicator : BitVec 8
  orderOrigination : BitVec 8
  hedgingInstruction : BitVec 8
  partyExecutingFirm : Alpha 5
  partyExecutingTrader : Alpha 6
  firmTradeId : Alpha 20
  freeText1 : Alpha 12
  freeText2 : Alpha 12
  freeText3 : Alpha 12
  freeText5 : Alpha 132
  positionEffect : PositionEffect
  account : Alpha 2
  partyIdBeneficiary : Alpha 9
  custOrderHandlingInst : CustOrderHandlingInst
  partyIdOrderOriginationFirm : Alpha 7
  partyIdPositionAccount : Alpha 32
  partyIdLocationId : Alpha 2
  complianceText : Alpha 20
  partyIdTakeUpTradingFirm : Alpha 5
  partyEndClientIdentification : Alpha 20
  pad6 : Alpha 6
  srqsHitQuoteGrpComp : Bounded 1 SrqsHitQuoteGrpComp
  deriving DecidableEq, Repr

namespace SrqsHitQuoteRequest

def encode (message : SrqsHitQuoteRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 8 message.validUntilTime
    ++ (encodeUIntLE 8 message.underlyingQty
    ++ (encodeUIntLE 8 message.underlyingPriceStipValue
    ++ (encodeUIntLE 8 message.partyIdClientId
    ++ (encodeUIntLE 8 message.partyIdInvestmentDecisionMaker
    ++ (encodeUIntLE 8 message.executingTrader
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.negotiationId
    ++ (encodeUInt 1 message.orderAttributeLiquidityProvision
    ++ (encodeUInt 1 message.executingTraderQualifier
    ++ (encodeUInt 1 message.partyIdInvestmentDecisionMakerQualifier
    ++ (encodeUInt 1 message.tradingCapacity
    ++ (encodeUInt 1 message.tradePublishIndicator
    ++ (encodeUInt 1 message.orderOrigination
    ++ (encodeUInt 1 message.hedgingInstruction
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.srqsHitQuoteGrpComp.val.length)
    ++ (Alpha.encode message.partyExecutingFirm
    ++ (Alpha.encode message.partyExecutingTrader
    ++ (Alpha.encode message.firmTradeId
    ++ (Alpha.encode message.freeText1
    ++ (Alpha.encode message.freeText2
    ++ (Alpha.encode message.freeText3
    ++ (Alpha.encode message.freeText5
    ++ (PositionEffect.encode message.positionEffect
    ++ (Alpha.encode message.account
    ++ (Alpha.encode message.partyIdBeneficiary
    ++ (CustOrderHandlingInst.encode message.custOrderHandlingInst
    ++ (Alpha.encode message.partyIdOrderOriginationFirm
    ++ (Alpha.encode message.partyIdPositionAccount
    ++ (Alpha.encode message.partyIdLocationId
    ++ (Alpha.encode message.complianceText
    ++ (Alpha.encode message.partyIdTakeUpTradingFirm
    ++ (Alpha.encode message.partyEndClientIdentification
    ++ (Alpha.encode message.pad6
    ++ (encodeMany SrqsHitQuoteGrpComp.encode message.srqsHitQuoteGrpComp.val)))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (SrqsHitQuoteRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (validUntilTime, bytes) ← decodeUIntLE 8 bytes
  let (underlyingQty, bytes) ← decodeUIntLE 8 bytes
  let (underlyingPriceStipValue, bytes) ← decodeUIntLE 8 bytes
  let (partyIdClientId, bytes) ← decodeUIntLE 8 bytes
  let (partyIdInvestmentDecisionMaker, bytes) ← decodeUIntLE 8 bytes
  let (executingTrader, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (negotiationId, bytes) ← decodeUIntLE 4 bytes
  let (orderAttributeLiquidityProvision, bytes) ← decodeUInt 1 bytes
  let (executingTraderQualifier, bytes) ← decodeUInt 1 bytes
  let (partyIdInvestmentDecisionMakerQualifier, bytes) ← decodeUInt 1 bytes
  let (tradingCapacity, bytes) ← decodeUInt 1 bytes
  let (tradePublishIndicator, bytes) ← decodeUInt 1 bytes
  let (orderOrigination, bytes) ← decodeUInt 1 bytes
  let (hedgingInstruction, bytes) ← decodeUInt 1 bytes
  let (noSrqsQuoteGrps, bytes) ← decodeUInt 1 bytes
  let (partyExecutingFirm, bytes) ← Alpha.decode 5 bytes
  let (partyExecutingTrader, bytes) ← Alpha.decode 6 bytes
  let (firmTradeId, bytes) ← Alpha.decode 20 bytes
  let (freeText1, bytes) ← Alpha.decode 12 bytes
  let (freeText2, bytes) ← Alpha.decode 12 bytes
  let (freeText3, bytes) ← Alpha.decode 12 bytes
  let (freeText5, bytes) ← Alpha.decode 132 bytes
  let (positionEffect, bytes) ← PositionEffect.decode bytes
  let (account, bytes) ← Alpha.decode 2 bytes
  let (partyIdBeneficiary, bytes) ← Alpha.decode 9 bytes
  let (custOrderHandlingInst, bytes) ← CustOrderHandlingInst.decode bytes
  let (partyIdOrderOriginationFirm, bytes) ← Alpha.decode 7 bytes
  let (partyIdPositionAccount, bytes) ← Alpha.decode 32 bytes
  let (partyIdLocationId, bytes) ← Alpha.decode 2 bytes
  let (complianceText, bytes) ← Alpha.decode 20 bytes
  let (partyIdTakeUpTradingFirm, bytes) ← Alpha.decode 5 bytes
  let (partyEndClientIdentification, bytes) ← Alpha.decode 20 bytes
  let (pad6, bytes) ← Alpha.decode 6 bytes
  let (srqsHitQuoteGrpComp_, bytes) ← decodeMany SrqsHitQuoteGrpComp.decode noSrqsQuoteGrps.toNat bytes
  if fits_srqsHitQuoteGrpComp : srqsHitQuoteGrpComp_.length < 256 ^ 1 then
    pure ({ networkMsgId, pad2, requestHeaderComp, validUntilTime, underlyingQty, underlyingPriceStipValue, partyIdClientId, partyIdInvestmentDecisionMaker, executingTrader, marketSegmentId, negotiationId, orderAttributeLiquidityProvision, executingTraderQualifier, partyIdInvestmentDecisionMakerQualifier, tradingCapacity, tradePublishIndicator, orderOrigination, hedgingInstruction, partyExecutingFirm, partyExecutingTrader, firmTradeId, freeText1, freeText2, freeText3, freeText5, positionEffect, account, partyIdBeneficiary, custOrderHandlingInst, partyIdOrderOriginationFirm, partyIdPositionAccount, partyIdLocationId, complianceText, partyIdTakeUpTradingFirm, partyEndClientIdentification, pad6, srqsHitQuoteGrpComp := ⟨srqsHitQuoteGrpComp_, fits_srqsHitQuoteGrpComp⟩ }, bytes)
  else none

theorem encode_length_pos (message : SrqsHitQuoteRequest) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SrqsHitQuoteRequest) : (encode message).length ≤ 6506 := by
  have bound_srqsHitQuoteGrpComp := message.srqsHitQuoteGrpComp.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length, PositionEffect.encode_length, CustOrderHandlingInst.encode_length, encodeMany_length_const SrqsHitQuoteGrpComp.encode 24 SrqsHitQuoteGrpComp.encode_length]
  omega

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : SrqsHitQuoteRequest) (rest : List UInt8) :
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
  rw [List.append_assoc, PositionEffect.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, CustOrderHandlingInst.decode_encode, some_bind]
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
  rw [decodeMany_bounded 1 SrqsHitQuoteGrpComp.encode SrqsHitQuoteGrpComp.decode SrqsHitQuoteGrpComp.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.srqsHitQuoteGrpComp.length_lt]
  rfl

end SrqsHitQuoteRequest

/-- Srqs Inquire Smart Respondent Request: 26 bytes -/
structure SrqsInquireSmartRespondentRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  marketSegmentId : BitVec 32
  eurexVolumeRanking : BitVec 8
  enlightRfqAvgRespTimeRanking : BitVec 8
  enlightRfqAvgRespRateRanking : BitVec 8
  tradeToQuoteRatioRanking : BitVec 8
  deriving DecidableEq, Repr

namespace SrqsInquireSmartRespondentRequest

def encode (message : SrqsInquireSmartRespondentRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUInt 1 message.eurexVolumeRanking
    ++ (encodeUInt 1 message.enlightRfqAvgRespTimeRanking
    ++ (encodeUInt 1 message.enlightRfqAvgRespRateRanking
    ++ (encodeUInt 1 message.tradeToQuoteRatioRanking)))))))

def decode (bytes : List UInt8) : Option (SrqsInquireSmartRespondentRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (eurexVolumeRanking, bytes) ← decodeUInt 1 bytes
  let (enlightRfqAvgRespTimeRanking, bytes) ← decodeUInt 1 bytes
  let (enlightRfqAvgRespRateRanking, bytes) ← decodeUInt 1 bytes
  let (tradeToQuoteRatioRanking, bytes) ← decodeUInt 1 bytes
  pure ({ networkMsgId, pad2, requestHeaderComp, marketSegmentId, eurexVolumeRanking, enlightRfqAvgRespTimeRanking, enlightRfqAvgRespRateRanking, tradeToQuoteRatioRanking }, bytes)

@[simp] theorem encode_length (message : SrqsInquireSmartRespondentRequest) : (encode message).length = 26 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : SrqsInquireSmartRespondentRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SrqsInquireSmartRespondentRequest) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end SrqsInquireSmartRespondentRequest

/-- Quot Req Legs Grp Comp: 24 bytes -/
structure QuotReqLegsGrpComp where
  legSecurityId : BitVec 64
  legRatioQty : BitVec 32
  legSymbol : BitVec 32
  legSecurityType : BitVec 8
  legSide : BitVec 8
  pad6 : Alpha 6
  deriving DecidableEq, Repr

namespace QuotReqLegsGrpComp

def encode (message : QuotReqLegsGrpComp) : List UInt8 :=
  encodeUIntLE 8 message.legSecurityId
    ++ (encodeUIntLE 4 message.legRatioQty
    ++ (encodeUIntLE 4 message.legSymbol
    ++ (encodeUInt 1 message.legSecurityType
    ++ (encodeUInt 1 message.legSide
    ++ (Alpha.encode message.pad6)))))

def decode (bytes : List UInt8) : Option (QuotReqLegsGrpComp × List UInt8) := do
  let (legSecurityId, bytes) ← decodeUIntLE 8 bytes
  let (legRatioQty, bytes) ← decodeUIntLE 4 bytes
  let (legSymbol, bytes) ← decodeUIntLE 4 bytes
  let (legSecurityType, bytes) ← decodeUInt 1 bytes
  let (legSide, bytes) ← decodeUInt 1 bytes
  let (pad6, bytes) ← Alpha.decode 6 bytes
  pure ({ legSecurityId, legRatioQty, legSymbol, legSecurityType, legSide, pad6 }, bytes)

@[simp] theorem encode_length (message : QuotReqLegsGrpComp) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : QuotReqLegsGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : QuotReqLegsGrpComp) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end QuotReqLegsGrpComp

/-- Target Parties Comp: 32 bytes -/
structure TargetPartiesComp where
  targetPartyIdExecutingTrader : BitVec 32
  sideDisclosureInstruction : BitVec 8
  priceDisclosureInstruction : BitVec 8
  leavesQtyDisclosureInstruction : BitVec 8
  lastPxDisclosureInstruction : BitVec 8
  lastQtyDisclosureInstruction : BitVec 8
  freeText5DisclosureInstruction : BitVec 8
  partyOrderOriginationDisclosureInstruction : BitVec 8
  quoteInstruction : BitVec 8
  chargeIdDisclosureInstruction : BitVec 8
  targetPartyExecutingFirm : Alpha 5
  targetPartyExecutingTrader : Alpha 6
  partyDetailStatus : BitVec 8
  partyDetailStatusInformation : BitVec 8
  pad6 : Alpha 6
  deriving DecidableEq, Repr

namespace TargetPartiesComp

def encode (message : TargetPartiesComp) : List UInt8 :=
  encodeUIntLE 4 message.targetPartyIdExecutingTrader
    ++ (encodeUInt 1 message.sideDisclosureInstruction
    ++ (encodeUInt 1 message.priceDisclosureInstruction
    ++ (encodeUInt 1 message.leavesQtyDisclosureInstruction
    ++ (encodeUInt 1 message.lastPxDisclosureInstruction
    ++ (encodeUInt 1 message.lastQtyDisclosureInstruction
    ++ (encodeUInt 1 message.freeText5DisclosureInstruction
    ++ (encodeUInt 1 message.partyOrderOriginationDisclosureInstruction
    ++ (encodeUInt 1 message.quoteInstruction
    ++ (encodeUInt 1 message.chargeIdDisclosureInstruction
    ++ (Alpha.encode message.targetPartyExecutingFirm
    ++ (Alpha.encode message.targetPartyExecutingTrader
    ++ (encodeUInt 1 message.partyDetailStatus
    ++ (encodeUInt 1 message.partyDetailStatusInformation
    ++ (Alpha.encode message.pad6))))))))))))))

def decode (bytes : List UInt8) : Option (TargetPartiesComp × List UInt8) := do
  let (targetPartyIdExecutingTrader, bytes) ← decodeUIntLE 4 bytes
  let (sideDisclosureInstruction, bytes) ← decodeUInt 1 bytes
  let (priceDisclosureInstruction, bytes) ← decodeUInt 1 bytes
  let (leavesQtyDisclosureInstruction, bytes) ← decodeUInt 1 bytes
  let (lastPxDisclosureInstruction, bytes) ← decodeUInt 1 bytes
  let (lastQtyDisclosureInstruction, bytes) ← decodeUInt 1 bytes
  let (freeText5DisclosureInstruction, bytes) ← decodeUInt 1 bytes
  let (partyOrderOriginationDisclosureInstruction, bytes) ← decodeUInt 1 bytes
  let (quoteInstruction, bytes) ← decodeUInt 1 bytes
  let (chargeIdDisclosureInstruction, bytes) ← decodeUInt 1 bytes
  let (targetPartyExecutingFirm, bytes) ← Alpha.decode 5 bytes
  let (targetPartyExecutingTrader, bytes) ← Alpha.decode 6 bytes
  let (partyDetailStatus, bytes) ← decodeUInt 1 bytes
  let (partyDetailStatusInformation, bytes) ← decodeUInt 1 bytes
  let (pad6, bytes) ← Alpha.decode 6 bytes
  pure ({ targetPartyIdExecutingTrader, sideDisclosureInstruction, priceDisclosureInstruction, leavesQtyDisclosureInstruction, lastPxDisclosureInstruction, lastQtyDisclosureInstruction, freeText5DisclosureInstruction, partyOrderOriginationDisclosureInstruction, quoteInstruction, chargeIdDisclosureInstruction, targetPartyExecutingFirm, targetPartyExecutingTrader, partyDetailStatus, partyDetailStatusInformation, pad6 }, bytes)

@[simp] theorem encode_length (message : TargetPartiesComp) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : TargetPartiesComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TargetPartiesComp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end TargetPartiesComp

/-- Srqs Open Negotiation Request -/
structure SrqsOpenNegotiationRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  securityId : BitVec 64
  bidPx : BitVec 64
  offerPx : BitVec 64
  orderQty : BitVec 64
  quoteRefPrice : BitVec 64
  underlyingDeltaPercentage : BitVec 64
  validUntilTime : BitVec 64
  marketSegmentId : BitVec 32
  securitySubType : BitVec 32
  quoteType : BitVec 8
  quoteSubType : BitVec 8
  numberOfRespDisclosureInstruction : BitVec 8
  side : BitVec 8
  productComplex : BitVec 8
  respondentType : BitVec 8
  showLastDealOnClosure : BitVec 8
  bidPxIsLocked : BitVec 8
  offerPxIsLocked : BitVec 8
  sideIsLocked : BitVec 8
  orderQtyIsLocked : BitVec 8
  tradeAggregationTransType : BitVec 8
  quoteCondition : QuoteCondition
  partyExecutingFirm : Alpha 5
  partyExecutingTrader : Alpha 6
  freeText5 : Alpha 132
  quoteReqId : Alpha 20
  partyOrderOriginationTrader : Alpha 132
  chargeId : Alpha 132
  pad6 : Alpha 6
  quotReqLegsGrpComp : Bounded 1 QuotReqLegsGrpComp
  targetPartiesComp : Bounded 1 TargetPartiesComp
  deriving DecidableEq, Repr

namespace SrqsOpenNegotiationRequest

def encode (message : SrqsOpenNegotiationRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.bidPx
    ++ (encodeUIntLE 8 message.offerPx
    ++ (encodeUIntLE 8 message.orderQty
    ++ (encodeUIntLE 8 message.quoteRefPrice
    ++ (encodeUIntLE 8 message.underlyingDeltaPercentage
    ++ (encodeUIntLE 8 message.validUntilTime
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.securitySubType
    ++ (encodeUInt 1 message.quoteType
    ++ (encodeUInt 1 message.quoteSubType
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.quotReqLegsGrpComp.val.length)
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.targetPartiesComp.val.length)
    ++ (encodeUInt 1 message.numberOfRespDisclosureInstruction
    ++ (encodeUInt 1 message.side
    ++ (encodeUInt 1 message.productComplex
    ++ (encodeUInt 1 message.respondentType
    ++ (encodeUInt 1 message.showLastDealOnClosure
    ++ (encodeUInt 1 message.bidPxIsLocked
    ++ (encodeUInt 1 message.offerPxIsLocked
    ++ (encodeUInt 1 message.sideIsLocked
    ++ (encodeUInt 1 message.orderQtyIsLocked
    ++ (encodeUInt 1 message.tradeAggregationTransType
    ++ (QuoteCondition.encode message.quoteCondition
    ++ (Alpha.encode message.partyExecutingFirm
    ++ (Alpha.encode message.partyExecutingTrader
    ++ (Alpha.encode message.freeText5
    ++ (Alpha.encode message.quoteReqId
    ++ (Alpha.encode message.partyOrderOriginationTrader
    ++ (Alpha.encode message.chargeId
    ++ (Alpha.encode message.pad6
    ++ (encodeMany QuotReqLegsGrpComp.encode message.quotReqLegsGrpComp.val
    ++ (encodeMany TargetPartiesComp.encode message.targetPartiesComp.val)))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (SrqsOpenNegotiationRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (bidPx, bytes) ← decodeUIntLE 8 bytes
  let (offerPx, bytes) ← decodeUIntLE 8 bytes
  let (orderQty, bytes) ← decodeUIntLE 8 bytes
  let (quoteRefPrice, bytes) ← decodeUIntLE 8 bytes
  let (underlyingDeltaPercentage, bytes) ← decodeUIntLE 8 bytes
  let (validUntilTime, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (securitySubType, bytes) ← decodeUIntLE 4 bytes
  let (quoteType, bytes) ← decodeUInt 1 bytes
  let (quoteSubType, bytes) ← decodeUInt 1 bytes
  let (noLegs, bytes) ← decodeUInt 1 bytes
  let (noTargetPartyIDs, bytes) ← decodeUInt 1 bytes
  let (numberOfRespDisclosureInstruction, bytes) ← decodeUInt 1 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (productComplex, bytes) ← decodeUInt 1 bytes
  let (respondentType, bytes) ← decodeUInt 1 bytes
  let (showLastDealOnClosure, bytes) ← decodeUInt 1 bytes
  let (bidPxIsLocked, bytes) ← decodeUInt 1 bytes
  let (offerPxIsLocked, bytes) ← decodeUInt 1 bytes
  let (sideIsLocked, bytes) ← decodeUInt 1 bytes
  let (orderQtyIsLocked, bytes) ← decodeUInt 1 bytes
  let (tradeAggregationTransType, bytes) ← decodeUInt 1 bytes
  let (quoteCondition, bytes) ← QuoteCondition.decode bytes
  let (partyExecutingFirm, bytes) ← Alpha.decode 5 bytes
  let (partyExecutingTrader, bytes) ← Alpha.decode 6 bytes
  let (freeText5, bytes) ← Alpha.decode 132 bytes
  let (quoteReqId, bytes) ← Alpha.decode 20 bytes
  let (partyOrderOriginationTrader, bytes) ← Alpha.decode 132 bytes
  let (chargeId, bytes) ← Alpha.decode 132 bytes
  let (pad6, bytes) ← Alpha.decode 6 bytes
  let (quotReqLegsGrpComp_, bytes) ← decodeMany QuotReqLegsGrpComp.decode noLegs.toNat bytes
  let (targetPartiesComp_, bytes) ← decodeMany TargetPartiesComp.decode noTargetPartyIDs.toNat bytes
  if fits_quotReqLegsGrpComp : quotReqLegsGrpComp_.length < 256 ^ 1 then
    if fits_targetPartiesComp : targetPartiesComp_.length < 256 ^ 1 then
      pure ({ networkMsgId, pad2, requestHeaderComp, securityId, bidPx, offerPx, orderQty, quoteRefPrice, underlyingDeltaPercentage, validUntilTime, marketSegmentId, securitySubType, quoteType, quoteSubType, numberOfRespDisclosureInstruction, side, productComplex, respondentType, showLastDealOnClosure, bidPxIsLocked, offerPxIsLocked, sideIsLocked, orderQtyIsLocked, tradeAggregationTransType, quoteCondition, partyExecutingFirm, partyExecutingTrader, freeText5, quoteReqId, partyOrderOriginationTrader, chargeId, pad6, quotReqLegsGrpComp := ⟨quotReqLegsGrpComp_, fits_quotReqLegsGrpComp⟩, targetPartiesComp := ⟨targetPartiesComp_, fits_targetPartiesComp⟩ }, bytes)
    else none
  else none

theorem encode_length_pos (message : SrqsOpenNegotiationRequest) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SrqsOpenNegotiationRequest) : (encode message).length ≤ 14810 := by
  have bound_quotReqLegsGrpComp := message.quotReqLegsGrpComp.length_lt
  have bound_targetPartiesComp := message.targetPartiesComp.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length, QuoteCondition.encode_length, encodeMany_length_const QuotReqLegsGrpComp.encode 24 QuotReqLegsGrpComp.encode_length, encodeMany_length_const TargetPartiesComp.encode 32 TargetPartiesComp.encode_length]
  omega

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : SrqsOpenNegotiationRequest) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, QuoteCondition.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeMany_bounded 1 QuotReqLegsGrpComp.encode QuotReqLegsGrpComp.decode QuotReqLegsGrpComp.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 TargetPartiesComp.encode TargetPartiesComp.decode TargetPartiesComp.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.quotReqLegsGrpComp.length_lt, dite_eq_left message.targetPartiesComp.length_lt]
  rfl

end SrqsOpenNegotiationRequest

/-- Srqs Quote Snapshot Request: 18 bytes -/
structure SrqsQuoteSnapshotRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  deriving DecidableEq, Repr

namespace SrqsQuoteSnapshotRequest

def encode (message : SrqsQuoteSnapshotRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp))

def decode (bytes : List UInt8) : Option (SrqsQuoteSnapshotRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  pure ({ networkMsgId, pad2, requestHeaderComp }, bytes)

@[simp] theorem encode_length (message : SrqsQuoteSnapshotRequest) : (encode message).length = 18 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RequestHeaderComp.encode_length]

theorem encode_length_pos (message : SrqsQuoteSnapshotRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SrqsQuoteSnapshotRequest) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [RequestHeaderComp.decode_encode, some_bind]
  rfl

end SrqsQuoteSnapshotRequest

/-- Srqs Quoting Status Request: 170 bytes -/
structure SrqsQuotingStatusRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  marketSegmentId : BitVec 32
  negotiationId : BitVec 32
  quotingStatus : BitVec 8
  partyExecutingFirm : Alpha 5
  partyExecutingTrader : Alpha 6
  freeText5 : Alpha 132
  deriving DecidableEq, Repr

namespace SrqsQuotingStatusRequest

def encode (message : SrqsQuotingStatusRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.negotiationId
    ++ (encodeUInt 1 message.quotingStatus
    ++ (Alpha.encode message.partyExecutingFirm
    ++ (Alpha.encode message.partyExecutingTrader
    ++ (Alpha.encode message.freeText5))))))))

def decode (bytes : List UInt8) : Option (SrqsQuotingStatusRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (negotiationId, bytes) ← decodeUIntLE 4 bytes
  let (quotingStatus, bytes) ← decodeUInt 1 bytes
  let (partyExecutingFirm, bytes) ← Alpha.decode 5 bytes
  let (partyExecutingTrader, bytes) ← Alpha.decode 6 bytes
  let (freeText5, bytes) ← Alpha.decode 132 bytes
  pure ({ networkMsgId, pad2, requestHeaderComp, marketSegmentId, negotiationId, quotingStatus, partyExecutingFirm, partyExecutingTrader, freeText5 }, bytes)

@[simp] theorem encode_length (message : SrqsQuotingStatusRequest) : (encode message).length = 170 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : SrqsQuotingStatusRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SrqsQuotingStatusRequest) (rest : List UInt8) :
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

end SrqsQuotingStatusRequest

/-- Srqs Update Deal Status Request: 202 bytes -/
structure SrqsUpdateDealStatusRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  underlyingPriceStipValue : BitVec 64
  underlyingPx : BitVec 64
  lastQty : BitVec 64
  marketSegmentId : BitVec 32
  negotiationId : BitVec 32
  tradeId : BitVec 32
  tradeReportType : BitVec 8
  trdRptStatus : BitVec 8
  partyExecutingFirm : Alpha 5
  partyExecutingTrader : Alpha 6
  freeText5 : Alpha 132
  pad3 : Alpha 3
  deriving DecidableEq, Repr

namespace SrqsUpdateDealStatusRequest

def encode (message : SrqsUpdateDealStatusRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 8 message.underlyingPriceStipValue
    ++ (encodeUIntLE 8 message.underlyingPx
    ++ (encodeUIntLE 8 message.lastQty
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.negotiationId
    ++ (encodeUIntLE 4 message.tradeId
    ++ (encodeUInt 1 message.tradeReportType
    ++ (encodeUInt 1 message.trdRptStatus
    ++ (Alpha.encode message.partyExecutingFirm
    ++ (Alpha.encode message.partyExecutingTrader
    ++ (Alpha.encode message.freeText5
    ++ (Alpha.encode message.pad3))))))))))))))

def decode (bytes : List UInt8) : Option (SrqsUpdateDealStatusRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (underlyingPriceStipValue, bytes) ← decodeUIntLE 8 bytes
  let (underlyingPx, bytes) ← decodeUIntLE 8 bytes
  let (lastQty, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (negotiationId, bytes) ← decodeUIntLE 4 bytes
  let (tradeId, bytes) ← decodeUIntLE 4 bytes
  let (tradeReportType, bytes) ← decodeUInt 1 bytes
  let (trdRptStatus, bytes) ← decodeUInt 1 bytes
  let (partyExecutingFirm, bytes) ← Alpha.decode 5 bytes
  let (partyExecutingTrader, bytes) ← Alpha.decode 6 bytes
  let (freeText5, bytes) ← Alpha.decode 132 bytes
  let (pad3, bytes) ← Alpha.decode 3 bytes
  pure ({ networkMsgId, pad2, requestHeaderComp, underlyingPriceStipValue, underlyingPx, lastQty, marketSegmentId, negotiationId, tradeId, tradeReportType, trdRptStatus, partyExecutingFirm, partyExecutingTrader, freeText5, pad3 }, bytes)

@[simp] theorem encode_length (message : SrqsUpdateDealStatusRequest) : (encode message).length = 202 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : SrqsUpdateDealStatusRequest) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SrqsUpdateDealStatusRequest) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SrqsUpdateDealStatusRequest

/-- Srqs Update Negotiation Request -/
structure SrqsUpdateNegotiationRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  quoteRefPrice : BitVec 64
  underlyingDeltaPercentage : BitVec 64
  bidPx : BitVec 64
  offerPx : BitVec 64
  orderQty : BitVec 64
  marketSegmentId : BitVec 32
  negotiationId : BitVec 32
  numberOfRespDisclosureInstruction : BitVec 8
  side : BitVec 8
  showLastDealOnClosure : BitVec 8
  quoteType : BitVec 8
  quoteSubType : BitVec 8
  respondentType : BitVec 8
  tradeAggregationTransType : BitVec 8
  quoteCondition : QuoteCondition
  partyExecutingFirm : Alpha 5
  partyExecutingTrader : Alpha 6
  freeText5 : Alpha 132
  partyOrderOriginationTrader : Alpha 132
  chargeId : Alpha 132
  targetPartiesComp : Bounded 1 TargetPartiesComp
  deriving DecidableEq, Repr

namespace SrqsUpdateNegotiationRequest

def encode (message : SrqsUpdateNegotiationRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 8 message.quoteRefPrice
    ++ (encodeUIntLE 8 message.underlyingDeltaPercentage
    ++ (encodeUIntLE 8 message.bidPx
    ++ (encodeUIntLE 8 message.offerPx
    ++ (encodeUIntLE 8 message.orderQty
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.negotiationId
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.targetPartiesComp.val.length)
    ++ (encodeUInt 1 message.numberOfRespDisclosureInstruction
    ++ (encodeUInt 1 message.side
    ++ (encodeUInt 1 message.showLastDealOnClosure
    ++ (encodeUInt 1 message.quoteType
    ++ (encodeUInt 1 message.quoteSubType
    ++ (encodeUInt 1 message.respondentType
    ++ (encodeUInt 1 message.tradeAggregationTransType
    ++ (QuoteCondition.encode message.quoteCondition
    ++ (Alpha.encode message.partyExecutingFirm
    ++ (Alpha.encode message.partyExecutingTrader
    ++ (Alpha.encode message.freeText5
    ++ (Alpha.encode message.partyOrderOriginationTrader
    ++ (Alpha.encode message.chargeId
    ++ (encodeMany TargetPartiesComp.encode message.targetPartiesComp.val))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (SrqsUpdateNegotiationRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (quoteRefPrice, bytes) ← decodeUIntLE 8 bytes
  let (underlyingDeltaPercentage, bytes) ← decodeUIntLE 8 bytes
  let (bidPx, bytes) ← decodeUIntLE 8 bytes
  let (offerPx, bytes) ← decodeUIntLE 8 bytes
  let (orderQty, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (negotiationId, bytes) ← decodeUIntLE 4 bytes
  let (noTargetPartyIDs, bytes) ← decodeUInt 1 bytes
  let (numberOfRespDisclosureInstruction, bytes) ← decodeUInt 1 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (showLastDealOnClosure, bytes) ← decodeUInt 1 bytes
  let (quoteType, bytes) ← decodeUInt 1 bytes
  let (quoteSubType, bytes) ← decodeUInt 1 bytes
  let (respondentType, bytes) ← decodeUInt 1 bytes
  let (tradeAggregationTransType, bytes) ← decodeUInt 1 bytes
  let (quoteCondition, bytes) ← QuoteCondition.decode bytes
  let (partyExecutingFirm, bytes) ← Alpha.decode 5 bytes
  let (partyExecutingTrader, bytes) ← Alpha.decode 6 bytes
  let (freeText5, bytes) ← Alpha.decode 132 bytes
  let (partyOrderOriginationTrader, bytes) ← Alpha.decode 132 bytes
  let (chargeId, bytes) ← Alpha.decode 132 bytes
  let (targetPartiesComp_, bytes) ← decodeMany TargetPartiesComp.decode noTargetPartyIDs.toNat bytes
  if fits_targetPartiesComp : targetPartiesComp_.length < 256 ^ 1 then
    pure ({ networkMsgId, pad2, requestHeaderComp, quoteRefPrice, underlyingDeltaPercentage, bidPx, offerPx, orderQty, marketSegmentId, negotiationId, numberOfRespDisclosureInstruction, side, showLastDealOnClosure, quoteType, quoteSubType, respondentType, tradeAggregationTransType, quoteCondition, partyExecutingFirm, partyExecutingTrader, freeText5, partyOrderOriginationTrader, chargeId, targetPartiesComp := ⟨targetPartiesComp_, fits_targetPartiesComp⟩ }, bytes)
  else none

theorem encode_length_pos (message : SrqsUpdateNegotiationRequest) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SrqsUpdateNegotiationRequest) : (encode message).length ≤ 8642 := by
  have bound_targetPartiesComp := message.targetPartiesComp.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length, QuoteCondition.encode_length, encodeMany_length_const TargetPartiesComp.encode 32 TargetPartiesComp.encode_length]
  omega

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : SrqsUpdateNegotiationRequest) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, QuoteCondition.decode_encode, some_bind]
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
  rw [decodeMany_bounded 1 TargetPartiesComp.encode TargetPartiesComp.decode TargetPartiesComp.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.targetPartiesComp.length_lt]
  rfl

end SrqsUpdateNegotiationRequest

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

/-- Rra Update Base Party Grp Comp: 32 bytes -/
structure RraUpdateBasePartyGrpComp where
  remainingRiskAllowanceBaseLong : BitVec 64
  remainingRiskAllowanceBaseShort : BitVec 64
  riskLimitId : BitVec 32
  partyDetailExecutingUnit : Alpha 5
  pad7 : Alpha 7
  deriving DecidableEq, Repr

namespace RraUpdateBasePartyGrpComp

def encode (message : RraUpdateBasePartyGrpComp) : List UInt8 :=
  encodeUIntLE 8 message.remainingRiskAllowanceBaseLong
    ++ (encodeUIntLE 8 message.remainingRiskAllowanceBaseShort
    ++ (encodeUIntLE 4 message.riskLimitId
    ++ (Alpha.encode message.partyDetailExecutingUnit
    ++ (Alpha.encode message.pad7))))

def decode (bytes : List UInt8) : Option (RraUpdateBasePartyGrpComp × List UInt8) := do
  let (remainingRiskAllowanceBaseLong, bytes) ← decodeUIntLE 8 bytes
  let (remainingRiskAllowanceBaseShort, bytes) ← decodeUIntLE 8 bytes
  let (riskLimitId, bytes) ← decodeUIntLE 4 bytes
  let (partyDetailExecutingUnit, bytes) ← Alpha.decode 5 bytes
  let (pad7, bytes) ← Alpha.decode 7 bytes
  pure ({ remainingRiskAllowanceBaseLong, remainingRiskAllowanceBaseShort, riskLimitId, partyDetailExecutingUnit, pad7 }, bytes)

@[simp] theorem encode_length (message : RraUpdateBasePartyGrpComp) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : RraUpdateBasePartyGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RraUpdateBasePartyGrpComp) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
  rfl

end RraUpdateBasePartyGrpComp

/-- Update Remaining Risk Allowance Base Request -/
structure UpdateRemainingRiskAllowanceBaseRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  partitionId : BitVec 16
  pad4 : Alpha 4
  rraUpdateBasePartyGrpComp : Bounded 2 RraUpdateBasePartyGrpComp
  deriving DecidableEq, Repr

namespace UpdateRemainingRiskAllowanceBaseRequest

def encode (message : UpdateRemainingRiskAllowanceBaseRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 2 message.partitionId
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.rraUpdateBasePartyGrpComp.val.length)
    ++ (Alpha.encode message.pad4
    ++ (encodeMany RraUpdateBasePartyGrpComp.encode message.rraUpdateBasePartyGrpComp.val))))))

def decode (bytes : List UInt8) : Option (UpdateRemainingRiskAllowanceBaseRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (partitionId, bytes) ← decodeUIntLE 2 bytes
  let (noPartyRiskLimits, bytes) ← decodeUIntLE 2 bytes
  let (pad4, bytes) ← Alpha.decode 4 bytes
  let (rraUpdateBasePartyGrpComp_, bytes) ← decodeMany RraUpdateBasePartyGrpComp.decode noPartyRiskLimits.toNat bytes
  if fits_rraUpdateBasePartyGrpComp : rraUpdateBasePartyGrpComp_.length < 256 ^ 2 then
    pure ({ networkMsgId, pad2, requestHeaderComp, partitionId, pad4, rraUpdateBasePartyGrpComp := ⟨rraUpdateBasePartyGrpComp_, fits_rraUpdateBasePartyGrpComp⟩ }, bytes)
  else none

theorem encode_length_pos (message : UpdateRemainingRiskAllowanceBaseRequest) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : UpdateRemainingRiskAllowanceBaseRequest) : (encode message).length ≤ 2097146 := by
  have bound_rraUpdateBasePartyGrpComp := message.rraUpdateBasePartyGrpComp.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length, encodeMany_length_const RraUpdateBasePartyGrpComp.encode 32 RraUpdateBasePartyGrpComp.encode_length]
  omega

@[simp] theorem decode_encode (message : UpdateRemainingRiskAllowanceBaseRequest) (rest : List UInt8) :
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
  rw [decodeMany_bounded 2 RraUpdateBasePartyGrpComp.encode RraUpdateBasePartyGrpComp.decode RraUpdateBasePartyGrpComp.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.rraUpdateBasePartyGrpComp.length_lt]
  rfl

end UpdateRemainingRiskAllowanceBaseRequest

/-- Side Alloc Ext Grp Comp: 200 bytes -/
structure SideAllocExtGrpComp where
  allocQty : BitVec 64
  partyIdClientId : BitVec 64
  partyIdInvestmentDecisionMaker : BitVec 64
  executingTrader : BitVec 64
  individualAllocId : BitVec 32
  partyExecutingFirm : Alpha 5
  partyExecutingTrader : Alpha 6
  pad1 : Alpha 1
  tesEnrichmentRuleId : BitVec 32
  side : BitVec 8
  tradeAllocStatus : BitVec 8
  tradingCapacity : BitVec 8
  positionEffect : PositionEffect
  orderAttributeLiquidityProvision : BitVec 8
  executingTraderQualifier : BitVec 8
  partyIdInvestmentDecisionMakerQualifier : BitVec 8
  orderAttributeRiskReduction : BitVec 8
  orderOrigination : BitVec 8
  account : Alpha 2
  partyIdPositionAccount : Alpha 32
  partyIdTakeUpTradingFirm : Alpha 5
  freeText1 : Alpha 12
  freeText2 : Alpha 12
  freeText3 : Alpha 12
  partyIdOrderOriginationFirm : Alpha 7
  partyIdBeneficiary : Alpha 9
  partyIdLocationId : Alpha 2
  custOrderHandlingInst : CustOrderHandlingInst
  complianceText : Alpha 20
  partyEndClientIdentification : Alpha 20
  pad5 : Alpha 5
  deriving DecidableEq, Repr

namespace SideAllocExtGrpComp

def encode (message : SideAllocExtGrpComp) : List UInt8 :=
  encodeUIntLE 8 message.allocQty
    ++ (encodeUIntLE 8 message.partyIdClientId
    ++ (encodeUIntLE 8 message.partyIdInvestmentDecisionMaker
    ++ (encodeUIntLE 8 message.executingTrader
    ++ (encodeUIntLE 4 message.individualAllocId
    ++ (Alpha.encode message.partyExecutingFirm
    ++ (Alpha.encode message.partyExecutingTrader
    ++ (Alpha.encode message.pad1
    ++ (encodeUIntLE 4 message.tesEnrichmentRuleId
    ++ (encodeUInt 1 message.side
    ++ (encodeUInt 1 message.tradeAllocStatus
    ++ (encodeUInt 1 message.tradingCapacity
    ++ (PositionEffect.encode message.positionEffect
    ++ (encodeUInt 1 message.orderAttributeLiquidityProvision
    ++ (encodeUInt 1 message.executingTraderQualifier
    ++ (encodeUInt 1 message.partyIdInvestmentDecisionMakerQualifier
    ++ (encodeUInt 1 message.orderAttributeRiskReduction
    ++ (encodeUInt 1 message.orderOrigination
    ++ (Alpha.encode message.account
    ++ (Alpha.encode message.partyIdPositionAccount
    ++ (Alpha.encode message.partyIdTakeUpTradingFirm
    ++ (Alpha.encode message.freeText1
    ++ (Alpha.encode message.freeText2
    ++ (Alpha.encode message.freeText3
    ++ (Alpha.encode message.partyIdOrderOriginationFirm
    ++ (Alpha.encode message.partyIdBeneficiary
    ++ (Alpha.encode message.partyIdLocationId
    ++ (CustOrderHandlingInst.encode message.custOrderHandlingInst
    ++ (Alpha.encode message.complianceText
    ++ (Alpha.encode message.partyEndClientIdentification
    ++ (Alpha.encode message.pad5))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (SideAllocExtGrpComp × List UInt8) := do
  let (allocQty, bytes) ← decodeUIntLE 8 bytes
  let (partyIdClientId, bytes) ← decodeUIntLE 8 bytes
  let (partyIdInvestmentDecisionMaker, bytes) ← decodeUIntLE 8 bytes
  let (executingTrader, bytes) ← decodeUIntLE 8 bytes
  let (individualAllocId, bytes) ← decodeUIntLE 4 bytes
  let (partyExecutingFirm, bytes) ← Alpha.decode 5 bytes
  let (partyExecutingTrader, bytes) ← Alpha.decode 6 bytes
  let (pad1, bytes) ← Alpha.decode 1 bytes
  let (tesEnrichmentRuleId, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (tradeAllocStatus, bytes) ← decodeUInt 1 bytes
  let (tradingCapacity, bytes) ← decodeUInt 1 bytes
  let (positionEffect, bytes) ← PositionEffect.decode bytes
  let (orderAttributeLiquidityProvision, bytes) ← decodeUInt 1 bytes
  let (executingTraderQualifier, bytes) ← decodeUInt 1 bytes
  let (partyIdInvestmentDecisionMakerQualifier, bytes) ← decodeUInt 1 bytes
  let (orderAttributeRiskReduction, bytes) ← decodeUInt 1 bytes
  let (orderOrigination, bytes) ← decodeUInt 1 bytes
  let (account, bytes) ← Alpha.decode 2 bytes
  let (partyIdPositionAccount, bytes) ← Alpha.decode 32 bytes
  let (partyIdTakeUpTradingFirm, bytes) ← Alpha.decode 5 bytes
  let (freeText1, bytes) ← Alpha.decode 12 bytes
  let (freeText2, bytes) ← Alpha.decode 12 bytes
  let (freeText3, bytes) ← Alpha.decode 12 bytes
  let (partyIdOrderOriginationFirm, bytes) ← Alpha.decode 7 bytes
  let (partyIdBeneficiary, bytes) ← Alpha.decode 9 bytes
  let (partyIdLocationId, bytes) ← Alpha.decode 2 bytes
  let (custOrderHandlingInst, bytes) ← CustOrderHandlingInst.decode bytes
  let (complianceText, bytes) ← Alpha.decode 20 bytes
  let (partyEndClientIdentification, bytes) ← Alpha.decode 20 bytes
  let (pad5, bytes) ← Alpha.decode 5 bytes
  pure ({ allocQty, partyIdClientId, partyIdInvestmentDecisionMaker, executingTrader, individualAllocId, partyExecutingFirm, partyExecutingTrader, pad1, tesEnrichmentRuleId, side, tradeAllocStatus, tradingCapacity, positionEffect, orderAttributeLiquidityProvision, executingTraderQualifier, partyIdInvestmentDecisionMakerQualifier, orderAttributeRiskReduction, orderOrigination, account, partyIdPositionAccount, partyIdTakeUpTradingFirm, freeText1, freeText2, freeText3, partyIdOrderOriginationFirm, partyIdBeneficiary, partyIdLocationId, custOrderHandlingInst, complianceText, partyEndClientIdentification, pad5 }, bytes)

@[simp] theorem encode_length (message : SideAllocExtGrpComp) : (encode message).length = 200 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length, PositionEffect.encode_length, CustOrderHandlingInst.encode_length]

theorem encode_length_pos (message : SideAllocExtGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : SideAllocExtGrpComp) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, PositionEffect.decode_encode, some_bind]
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
  rw [List.append_assoc, CustOrderHandlingInst.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SideAllocExtGrpComp

/-- Upload Tes Trade Request -/
structure UploadTesTradeRequest where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  securityId : BitVec 64
  lastPx : BitVec 64
  transBkdTime : BitVec 64
  underlyingPx : BitVec 64
  relatedClosePrice : BitVec 64
  relatedTradeQuantity : BitVec 64
  relatedSecurityId : BitVec 64
  relatedPx : BitVec 64
  underlyingQty : BitVec 64
  marketSegmentId : BitVec 32
  underlyingSettlementDate : BitVec 32
  underlyingMaturityDate : BitVec 32
  relatedTradeId : BitVec 32
  relatedMarketSegmentId : BitVec 32
  trdType : BitVec 16
  productComplex : BitVec 8
  tradeReportType : BitVec 8
  tradePublishIndicator : BitVec 8
  skipValidations : BitVec 8
  trdRptStatus : BitVec 8
  tradePlatform : BitVec 8
  hedgeType : BitVec 8
  partyIdSettlementLocation : BitVec 8
  valueCheckTypeMinLotSize : BitVec 8
  tradeReportId : Alpha 20
  tradeReportText : Alpha 20
  underlyingSecurityId : Alpha 12
  underlyingSecurityDesc : Alpha 30
  underlyingCurrency : Alpha 3
  underlyingIssuer : Alpha 30
  swapClearer : BitVec 8
  sideAllocExtGrpComp : Bounded 1 SideAllocExtGrpComp
  trdInstrmntLegGrpComp : Bounded 1 TrdInstrmntLegGrpComp
  instrumentEventGrpComp : Bounded 1 InstrumentEventGrpComp
  instrumentAttributeGrpComp : Bounded 1 InstrumentAttributeGrpComp
  underlyingStipGrpComp : Bounded 1 UnderlyingStipGrpComp
  deriving DecidableEq, Repr

namespace UploadTesTradeRequest

def encode (message : UploadTesTradeRequest) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.lastPx
    ++ (encodeUIntLE 8 message.transBkdTime
    ++ (encodeUIntLE 8 message.underlyingPx
    ++ (encodeUIntLE 8 message.relatedClosePrice
    ++ (encodeUIntLE 8 message.relatedTradeQuantity
    ++ (encodeUIntLE 8 message.relatedSecurityId
    ++ (encodeUIntLE 8 message.relatedPx
    ++ (encodeUIntLE 8 message.underlyingQty
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.underlyingSettlementDate
    ++ (encodeUIntLE 4 message.underlyingMaturityDate
    ++ (encodeUIntLE 4 message.relatedTradeId
    ++ (encodeUIntLE 4 message.relatedMarketSegmentId
    ++ (encodeUIntLE 2 message.trdType
    ++ (encodeUInt 1 message.productComplex
    ++ (encodeUInt 1 message.tradeReportType
    ++ (encodeUInt 1 message.tradePublishIndicator
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.sideAllocExtGrpComp.val.length)
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.trdInstrmntLegGrpComp.val.length)
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.instrumentEventGrpComp.val.length)
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.instrumentAttributeGrpComp.val.length)
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.underlyingStipGrpComp.val.length)
    ++ (encodeUInt 1 message.skipValidations
    ++ (encodeUInt 1 message.trdRptStatus
    ++ (encodeUInt 1 message.tradePlatform
    ++ (encodeUInt 1 message.hedgeType
    ++ (encodeUInt 1 message.partyIdSettlementLocation
    ++ (encodeUInt 1 message.valueCheckTypeMinLotSize
    ++ (Alpha.encode message.tradeReportId
    ++ (Alpha.encode message.tradeReportText
    ++ (Alpha.encode message.underlyingSecurityId
    ++ (Alpha.encode message.underlyingSecurityDesc
    ++ (Alpha.encode message.underlyingCurrency
    ++ (Alpha.encode message.underlyingIssuer
    ++ (encodeUInt 1 message.swapClearer
    ++ (encodeMany SideAllocExtGrpComp.encode message.sideAllocExtGrpComp.val
    ++ (encodeMany TrdInstrmntLegGrpComp.encode message.trdInstrmntLegGrpComp.val
    ++ (encodeMany InstrumentEventGrpComp.encode message.instrumentEventGrpComp.val
    ++ (encodeMany InstrumentAttributeGrpComp.encode message.instrumentAttributeGrpComp.val
    ++ (encodeMany UnderlyingStipGrpComp.encode message.underlyingStipGrpComp.val)))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (UploadTesTradeRequest × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  let (transBkdTime, bytes) ← decodeUIntLE 8 bytes
  let (underlyingPx, bytes) ← decodeUIntLE 8 bytes
  let (relatedClosePrice, bytes) ← decodeUIntLE 8 bytes
  let (relatedTradeQuantity, bytes) ← decodeUIntLE 8 bytes
  let (relatedSecurityId, bytes) ← decodeUIntLE 8 bytes
  let (relatedPx, bytes) ← decodeUIntLE 8 bytes
  let (underlyingQty, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (underlyingSettlementDate, bytes) ← decodeUIntLE 4 bytes
  let (underlyingMaturityDate, bytes) ← decodeUIntLE 4 bytes
  let (relatedTradeId, bytes) ← decodeUIntLE 4 bytes
  let (relatedMarketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (trdType, bytes) ← decodeUIntLE 2 bytes
  let (productComplex, bytes) ← decodeUInt 1 bytes
  let (tradeReportType, bytes) ← decodeUInt 1 bytes
  let (tradePublishIndicator, bytes) ← decodeUInt 1 bytes
  let (noSideAllocs, bytes) ← decodeUInt 1 bytes
  let (noLegs, bytes) ← decodeUInt 1 bytes
  let (noEvents, bytes) ← decodeUInt 1 bytes
  let (noInstrAttrib, bytes) ← decodeUInt 1 bytes
  let (noUnderlyingStips, bytes) ← decodeUInt 1 bytes
  let (skipValidations, bytes) ← decodeUInt 1 bytes
  let (trdRptStatus, bytes) ← decodeUInt 1 bytes
  let (tradePlatform, bytes) ← decodeUInt 1 bytes
  let (hedgeType, bytes) ← decodeUInt 1 bytes
  let (partyIdSettlementLocation, bytes) ← decodeUInt 1 bytes
  let (valueCheckTypeMinLotSize, bytes) ← decodeUInt 1 bytes
  let (tradeReportId, bytes) ← Alpha.decode 20 bytes
  let (tradeReportText, bytes) ← Alpha.decode 20 bytes
  let (underlyingSecurityId, bytes) ← Alpha.decode 12 bytes
  let (underlyingSecurityDesc, bytes) ← Alpha.decode 30 bytes
  let (underlyingCurrency, bytes) ← Alpha.decode 3 bytes
  let (underlyingIssuer, bytes) ← Alpha.decode 30 bytes
  let (swapClearer, bytes) ← decodeUInt 1 bytes
  let (sideAllocExtGrpComp_, bytes) ← decodeMany SideAllocExtGrpComp.decode noSideAllocs.toNat bytes
  let (trdInstrmntLegGrpComp_, bytes) ← decodeMany TrdInstrmntLegGrpComp.decode noLegs.toNat bytes
  let (instrumentEventGrpComp_, bytes) ← decodeMany InstrumentEventGrpComp.decode noEvents.toNat bytes
  let (instrumentAttributeGrpComp_, bytes) ← decodeMany InstrumentAttributeGrpComp.decode noInstrAttrib.toNat bytes
  let (underlyingStipGrpComp_, bytes) ← decodeMany UnderlyingStipGrpComp.decode noUnderlyingStips.toNat bytes
  if fits_sideAllocExtGrpComp : sideAllocExtGrpComp_.length < 256 ^ 1 then
    if fits_trdInstrmntLegGrpComp : trdInstrmntLegGrpComp_.length < 256 ^ 1 then
      if fits_instrumentEventGrpComp : instrumentEventGrpComp_.length < 256 ^ 1 then
        if fits_instrumentAttributeGrpComp : instrumentAttributeGrpComp_.length < 256 ^ 1 then
          if fits_underlyingStipGrpComp : underlyingStipGrpComp_.length < 256 ^ 1 then
            pure ({ networkMsgId, pad2, requestHeaderComp, securityId, lastPx, transBkdTime, underlyingPx, relatedClosePrice, relatedTradeQuantity, relatedSecurityId, relatedPx, underlyingQty, marketSegmentId, underlyingSettlementDate, underlyingMaturityDate, relatedTradeId, relatedMarketSegmentId, trdType, productComplex, tradeReportType, tradePublishIndicator, skipValidations, trdRptStatus, tradePlatform, hedgeType, partyIdSettlementLocation, valueCheckTypeMinLotSize, tradeReportId, tradeReportText, underlyingSecurityId, underlyingSecurityDesc, underlyingCurrency, underlyingIssuer, swapClearer, sideAllocExtGrpComp := ⟨sideAllocExtGrpComp_, fits_sideAllocExtGrpComp⟩, trdInstrmntLegGrpComp := ⟨trdInstrmntLegGrpComp_, fits_trdInstrmntLegGrpComp⟩, instrumentEventGrpComp := ⟨instrumentEventGrpComp_, fits_instrumentEventGrpComp⟩, instrumentAttributeGrpComp := ⟨instrumentAttributeGrpComp_, fits_instrumentAttributeGrpComp⟩, underlyingStipGrpComp := ⟨underlyingStipGrpComp_, fits_underlyingStipGrpComp⟩ }, bytes)
          else none
        else none
      else none
    else none
  else none

theorem encode_length_pos (message : UploadTesTradeRequest) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : UploadTesTradeRequest) : (encode message).length ≤ 79802 := by
  have bound_sideAllocExtGrpComp := message.sideAllocExtGrpComp.length_lt
  have bound_trdInstrmntLegGrpComp := message.trdInstrmntLegGrpComp.length_lt
  have bound_instrumentEventGrpComp := message.instrumentEventGrpComp.length_lt
  have bound_instrumentAttributeGrpComp := message.instrumentAttributeGrpComp.length_lt
  have bound_underlyingStipGrpComp := message.underlyingStipGrpComp.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const SideAllocExtGrpComp.encode 200 SideAllocExtGrpComp.encode_length, encodeMany_length_const TrdInstrmntLegGrpComp.encode 24 TrdInstrmntLegGrpComp.encode_length, encodeMany_length_const InstrumentEventGrpComp.encode 8 InstrumentEventGrpComp.encode_length, encodeMany_length_const InstrumentAttributeGrpComp.encode 40 InstrumentAttributeGrpComp.encode_length, encodeMany_length_const UnderlyingStipGrpComp.encode 40 UnderlyingStipGrpComp.encode_length]
  omega

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : UploadTesTradeRequest) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeMany_bounded 1 SideAllocExtGrpComp.encode SideAllocExtGrpComp.decode SideAllocExtGrpComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeMany_bounded 1 TrdInstrmntLegGrpComp.encode TrdInstrmntLegGrpComp.decode TrdInstrmntLegGrpComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeMany_bounded 1 InstrumentEventGrpComp.encode InstrumentEventGrpComp.decode InstrumentEventGrpComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeMany_bounded 1 InstrumentAttributeGrpComp.encode InstrumentAttributeGrpComp.decode InstrumentAttributeGrpComp.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 UnderlyingStipGrpComp.encode UnderlyingStipGrpComp.decode UnderlyingStipGrpComp.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.sideAllocExtGrpComp.length_lt, dite_eq_left message.trdInstrmntLegGrpComp.length_lt, dite_eq_left message.instrumentEventGrpComp.length_lt, dite_eq_left message.instrumentAttributeGrpComp.length_lt, dite_eq_left message.underlyingStipGrpComp.length_lt]
  rfl

end UploadTesTradeRequest

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

/-- User Login Request Encrypted: 706 bytes -/
structure UserLoginRequestEncrypted where
  networkMsgId : Alpha 8
  pad2 : Alpha 2
  requestHeaderComp : RequestHeaderComp
  username : BitVec 32
  encryptedPassword : Alpha 684
  deriving DecidableEq, Repr

namespace UserLoginRequestEncrypted

def encode (message : UserLoginRequestEncrypted) : List UInt8 :=
  Alpha.encode message.networkMsgId
    ++ (Alpha.encode message.pad2
    ++ (RequestHeaderComp.encode message.requestHeaderComp
    ++ (encodeUIntLE 4 message.username
    ++ (Alpha.encode message.encryptedPassword))))

def decode (bytes : List UInt8) : Option (UserLoginRequestEncrypted × List UInt8) := do
  let (networkMsgId, bytes) ← Alpha.decode 8 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (requestHeaderComp, bytes) ← RequestHeaderComp.decode bytes
  let (username, bytes) ← decodeUIntLE 4 bytes
  let (encryptedPassword, bytes) ← Alpha.decode 684 bytes
  pure ({ networkMsgId, pad2, requestHeaderComp, username, encryptedPassword }, bytes)

@[simp] theorem encode_length (message : UserLoginRequestEncrypted) : (encode message).length = 706 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RequestHeaderComp.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : UserLoginRequestEncrypted) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UserLoginRequestEncrypted) (rest : List UInt8) :
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

end UserLoginRequestEncrypted

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

/-- Any Client Payload, selected by Template Id -/
inductive ClientPayload where
  | addComplexInstrumentRequest (message : AddComplexInstrumentRequest) -- 10301
  | addFlexibleInstrumentRequest (message : AddFlexibleInstrumentRequest) -- 10309
  | addScaledSimpleInstrumentRequest (message : AddScaledSimpleInstrumentRequest) -- 10327
  | amendBasketTradeRequest (message : AmendBasketTradeRequest) -- 10629
  | approveBasketTradeRequest (message : ApproveBasketTradeRequest) -- 10623
  | approveReverseTesTradeRequest (message : ApproveReverseTesTradeRequest) -- 10631
  | approveTesTradeRequest (message : ApproveTesTradeRequest) -- 10603
  | crossRequest (message : CrossRequest) -- 10118
  | deleteAllOrderRequest (message : DeleteAllOrderRequest) -- 10120
  | deleteAllQuoteRequest (message : DeleteAllQuoteRequest) -- 10408
  | deleteBasketTradeRequest (message : DeleteBasketTradeRequest) -- 10622
  | deleteClipRequest (message : DeleteClipRequest) -- 10132
  | deleteOrderComplexRequest (message : DeleteOrderComplexRequest) -- 10123
  | deleteOrderRequest (message : DeleteOrderRequest) -- 10142
  | deleteOrderSingleRequest (message : DeleteOrderSingleRequest) -- 10109
  | deleteTesTradeRequest (message : DeleteTesTradeRequest) -- 10602
  | enterBasketTradeRequest (message : EnterBasketTradeRequest) -- 10620
  | enterClipRequest (message : EnterClipRequest) -- 10131
  | enterTesTradeRequest (message : EnterTesTradeRequest) -- 10600
  | heartbeat (message : Heartbeat) -- 10011
  | inquireEnrichmentRuleIdListRequest (message : InquireEnrichmentRuleIdListRequest) -- 10040
  | inquireMmParameterRequest (message : InquireMmParameterRequest) -- 10305
  | inquireMarginBasedRiskLimitRequest (message : InquireMarginBasedRiskLimitRequest) -- 10323
  | inquirePreTradeRiskLimitsRequest (message : InquirePreTradeRiskLimitsRequest) -- 10311
  | inquireSessionListRequest (message : InquireSessionListRequest) -- 10035
  | inquireUserRequest (message : InquireUserRequest) -- 10038
  | logonRequest (message : LogonRequest) -- 10000
  | logonRequestEncrypted (message : LogonRequestEncrypted) -- 19000
  | logoutRequest (message : LogoutRequest) -- 10002
  | mmParameterDefinitionRequest (message : MmParameterDefinitionRequest) -- 10303
  | massOrder (message : MassOrder) -- 10115
  | massQuoteRequest (message : MassQuoteRequest) -- 10405
  | modifyBasketTradeRequest (message : ModifyBasketTradeRequest) -- 10621
  | modifyOrderComplexRequest (message : ModifyOrderComplexRequest) -- 10114
  | modifyOrderComplexShortRequest (message : ModifyOrderComplexShortRequest) -- 10130
  | modifyOrderRequest (message : ModifyOrderRequest) -- 10140
  | modifyOrderShortRequest (message : ModifyOrderShortRequest) -- 10141
  | modifyOrderSingleRequest (message : ModifyOrderSingleRequest) -- 10106
  | modifyOrderSingleShortRequest (message : ModifyOrderSingleShortRequest) -- 10126
  | modifyTesTradeRequest (message : ModifyTesTradeRequest) -- 10601
  | newOrderComplexRequest (message : NewOrderComplexRequest) -- 10113
  | newOrderComplexShortRequest (message : NewOrderComplexShortRequest) -- 10129
  | newOrderRequest (message : NewOrderRequest) -- 10138
  | newOrderShortRequest (message : NewOrderShortRequest) -- 10139
  | newOrderSingleRequest (message : NewOrderSingleRequest) -- 10100
  | newOrderSingleShortRequest (message : NewOrderSingleShortRequest) -- 10125
  | pingRequest (message : PingRequest) -- 10320
  | preTradeRiskLimitsDefinitionRequest (message : PreTradeRiskLimitsDefinitionRequest) -- 10312
  | quoteActivationRequest (message : QuoteActivationRequest) -- 10403
  | rfqRequest (message : RfqRequest) -- 10401
  | retransmitMeMessageRequest (message : RetransmitMeMessageRequest) -- 10026
  | retransmitRequest (message : RetransmitRequest) -- 10008
  | reverseTesTradeRequest (message : ReverseTesTradeRequest) -- 10630
  | srqsEnterQuoteRequest (message : SrqsEnterQuoteRequest) -- 10702
  | srqsHitQuoteRequest (message : SrqsHitQuoteRequest) -- 10704
  | srqsInquireSmartRespondentRequest (message : SrqsInquireSmartRespondentRequest) -- 10718
  | srqsOpenNegotiationRequest (message : SrqsOpenNegotiationRequest) -- 10700
  | srqsQuoteSnapshotRequest (message : SrqsQuoteSnapshotRequest) -- 10720
  | srqsQuotingStatusRequest (message : SrqsQuotingStatusRequest) -- 10717
  | srqsUpdateDealStatusRequest (message : SrqsUpdateDealStatusRequest) -- 10706
  | srqsUpdateNegotiationRequest (message : SrqsUpdateNegotiationRequest) -- 10701
  | subscribeRequest (message : SubscribeRequest) -- 10025
  | unsubscribeRequest (message : UnsubscribeRequest) -- 10006
  | updateRemainingRiskAllowanceBaseRequest (message : UpdateRemainingRiskAllowanceBaseRequest) -- 10325
  | uploadTesTradeRequest (message : UploadTesTradeRequest) -- 10612
  | userLoginRequest (message : UserLoginRequest) -- 10018
  | userLoginRequestEncrypted (message : UserLoginRequestEncrypted) -- 19018
  | userLogoutRequest (message : UserLogoutRequest) -- 10029
  deriving DecidableEq, Repr

namespace ClientPayload

/-- The Template Id each message is sent under -/
def tag : ClientPayload → BitVec 16
  | .addComplexInstrumentRequest _ => 10301
  | .addFlexibleInstrumentRequest _ => 10309
  | .addScaledSimpleInstrumentRequest _ => 10327
  | .amendBasketTradeRequest _ => 10629
  | .approveBasketTradeRequest _ => 10623
  | .approveReverseTesTradeRequest _ => 10631
  | .approveTesTradeRequest _ => 10603
  | .crossRequest _ => 10118
  | .deleteAllOrderRequest _ => 10120
  | .deleteAllQuoteRequest _ => 10408
  | .deleteBasketTradeRequest _ => 10622
  | .deleteClipRequest _ => 10132
  | .deleteOrderComplexRequest _ => 10123
  | .deleteOrderRequest _ => 10142
  | .deleteOrderSingleRequest _ => 10109
  | .deleteTesTradeRequest _ => 10602
  | .enterBasketTradeRequest _ => 10620
  | .enterClipRequest _ => 10131
  | .enterTesTradeRequest _ => 10600
  | .heartbeat _ => 10011
  | .inquireEnrichmentRuleIdListRequest _ => 10040
  | .inquireMmParameterRequest _ => 10305
  | .inquireMarginBasedRiskLimitRequest _ => 10323
  | .inquirePreTradeRiskLimitsRequest _ => 10311
  | .inquireSessionListRequest _ => 10035
  | .inquireUserRequest _ => 10038
  | .logonRequest _ => 10000
  | .logonRequestEncrypted _ => 19000
  | .logoutRequest _ => 10002
  | .mmParameterDefinitionRequest _ => 10303
  | .massOrder _ => 10115
  | .massQuoteRequest _ => 10405
  | .modifyBasketTradeRequest _ => 10621
  | .modifyOrderComplexRequest _ => 10114
  | .modifyOrderComplexShortRequest _ => 10130
  | .modifyOrderRequest _ => 10140
  | .modifyOrderShortRequest _ => 10141
  | .modifyOrderSingleRequest _ => 10106
  | .modifyOrderSingleShortRequest _ => 10126
  | .modifyTesTradeRequest _ => 10601
  | .newOrderComplexRequest _ => 10113
  | .newOrderComplexShortRequest _ => 10129
  | .newOrderRequest _ => 10138
  | .newOrderShortRequest _ => 10139
  | .newOrderSingleRequest _ => 10100
  | .newOrderSingleShortRequest _ => 10125
  | .pingRequest _ => 10320
  | .preTradeRiskLimitsDefinitionRequest _ => 10312
  | .quoteActivationRequest _ => 10403
  | .rfqRequest _ => 10401
  | .retransmitMeMessageRequest _ => 10026
  | .retransmitRequest _ => 10008
  | .reverseTesTradeRequest _ => 10630
  | .srqsEnterQuoteRequest _ => 10702
  | .srqsHitQuoteRequest _ => 10704
  | .srqsInquireSmartRespondentRequest _ => 10718
  | .srqsOpenNegotiationRequest _ => 10700
  | .srqsQuoteSnapshotRequest _ => 10720
  | .srqsQuotingStatusRequest _ => 10717
  | .srqsUpdateDealStatusRequest _ => 10706
  | .srqsUpdateNegotiationRequest _ => 10701
  | .subscribeRequest _ => 10025
  | .unsubscribeRequest _ => 10006
  | .updateRemainingRiskAllowanceBaseRequest _ => 10325
  | .uploadTesTradeRequest _ => 10612
  | .userLoginRequest _ => 10018
  | .userLoginRequestEncrypted _ => 19018
  | .userLogoutRequest _ => 10029

def encode : ClientPayload → List UInt8
  | .addComplexInstrumentRequest message => AddComplexInstrumentRequest.encode message
  | .addFlexibleInstrumentRequest message => AddFlexibleInstrumentRequest.encode message
  | .addScaledSimpleInstrumentRequest message => AddScaledSimpleInstrumentRequest.encode message
  | .amendBasketTradeRequest message => AmendBasketTradeRequest.encode message
  | .approveBasketTradeRequest message => ApproveBasketTradeRequest.encode message
  | .approveReverseTesTradeRequest message => ApproveReverseTesTradeRequest.encode message
  | .approveTesTradeRequest message => ApproveTesTradeRequest.encode message
  | .crossRequest message => CrossRequest.encode message
  | .deleteAllOrderRequest message => DeleteAllOrderRequest.encode message
  | .deleteAllQuoteRequest message => DeleteAllQuoteRequest.encode message
  | .deleteBasketTradeRequest message => DeleteBasketTradeRequest.encode message
  | .deleteClipRequest message => DeleteClipRequest.encode message
  | .deleteOrderComplexRequest message => DeleteOrderComplexRequest.encode message
  | .deleteOrderRequest message => DeleteOrderRequest.encode message
  | .deleteOrderSingleRequest message => DeleteOrderSingleRequest.encode message
  | .deleteTesTradeRequest message => DeleteTesTradeRequest.encode message
  | .enterBasketTradeRequest message => EnterBasketTradeRequest.encode message
  | .enterClipRequest message => EnterClipRequest.encode message
  | .enterTesTradeRequest message => EnterTesTradeRequest.encode message
  | .heartbeat message => Heartbeat.encode message
  | .inquireEnrichmentRuleIdListRequest message => InquireEnrichmentRuleIdListRequest.encode message
  | .inquireMmParameterRequest message => InquireMmParameterRequest.encode message
  | .inquireMarginBasedRiskLimitRequest message => InquireMarginBasedRiskLimitRequest.encode message
  | .inquirePreTradeRiskLimitsRequest message => InquirePreTradeRiskLimitsRequest.encode message
  | .inquireSessionListRequest message => InquireSessionListRequest.encode message
  | .inquireUserRequest message => InquireUserRequest.encode message
  | .logonRequest message => LogonRequest.encode message
  | .logonRequestEncrypted message => LogonRequestEncrypted.encode message
  | .logoutRequest message => LogoutRequest.encode message
  | .mmParameterDefinitionRequest message => MmParameterDefinitionRequest.encode message
  | .massOrder message => MassOrder.encode message
  | .massQuoteRequest message => MassQuoteRequest.encode message
  | .modifyBasketTradeRequest message => ModifyBasketTradeRequest.encode message
  | .modifyOrderComplexRequest message => ModifyOrderComplexRequest.encode message
  | .modifyOrderComplexShortRequest message => ModifyOrderComplexShortRequest.encode message
  | .modifyOrderRequest message => ModifyOrderRequest.encode message
  | .modifyOrderShortRequest message => ModifyOrderShortRequest.encode message
  | .modifyOrderSingleRequest message => ModifyOrderSingleRequest.encode message
  | .modifyOrderSingleShortRequest message => ModifyOrderSingleShortRequest.encode message
  | .modifyTesTradeRequest message => ModifyTesTradeRequest.encode message
  | .newOrderComplexRequest message => NewOrderComplexRequest.encode message
  | .newOrderComplexShortRequest message => NewOrderComplexShortRequest.encode message
  | .newOrderRequest message => NewOrderRequest.encode message
  | .newOrderShortRequest message => NewOrderShortRequest.encode message
  | .newOrderSingleRequest message => NewOrderSingleRequest.encode message
  | .newOrderSingleShortRequest message => NewOrderSingleShortRequest.encode message
  | .pingRequest message => PingRequest.encode message
  | .preTradeRiskLimitsDefinitionRequest message => PreTradeRiskLimitsDefinitionRequest.encode message
  | .quoteActivationRequest message => QuoteActivationRequest.encode message
  | .rfqRequest message => RfqRequest.encode message
  | .retransmitMeMessageRequest message => RetransmitMeMessageRequest.encode message
  | .retransmitRequest message => RetransmitRequest.encode message
  | .reverseTesTradeRequest message => ReverseTesTradeRequest.encode message
  | .srqsEnterQuoteRequest message => SrqsEnterQuoteRequest.encode message
  | .srqsHitQuoteRequest message => SrqsHitQuoteRequest.encode message
  | .srqsInquireSmartRespondentRequest message => SrqsInquireSmartRespondentRequest.encode message
  | .srqsOpenNegotiationRequest message => SrqsOpenNegotiationRequest.encode message
  | .srqsQuoteSnapshotRequest message => SrqsQuoteSnapshotRequest.encode message
  | .srqsQuotingStatusRequest message => SrqsQuotingStatusRequest.encode message
  | .srqsUpdateDealStatusRequest message => SrqsUpdateDealStatusRequest.encode message
  | .srqsUpdateNegotiationRequest message => SrqsUpdateNegotiationRequest.encode message
  | .subscribeRequest message => SubscribeRequest.encode message
  | .unsubscribeRequest message => UnsubscribeRequest.encode message
  | .updateRemainingRiskAllowanceBaseRequest message => UpdateRemainingRiskAllowanceBaseRequest.encode message
  | .uploadTesTradeRequest message => UploadTesTradeRequest.encode message
  | .userLoginRequest message => UserLoginRequest.encode message
  | .userLoginRequestEncrypted message => UserLoginRequestEncrypted.encode message
  | .userLogoutRequest message => UserLogoutRequest.encode message

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (ClientPayload × List UInt8) :=
  if tag = 10301 then (AddComplexInstrumentRequest.decode bytes).map fun (message, rest) => (.addComplexInstrumentRequest message, rest)
  else if tag = 10309 then (AddFlexibleInstrumentRequest.decode bytes).map fun (message, rest) => (.addFlexibleInstrumentRequest message, rest)
  else if tag = 10327 then (AddScaledSimpleInstrumentRequest.decode bytes).map fun (message, rest) => (.addScaledSimpleInstrumentRequest message, rest)
  else if tag = 10629 then (AmendBasketTradeRequest.decode bytes).map fun (message, rest) => (.amendBasketTradeRequest message, rest)
  else if tag = 10623 then (ApproveBasketTradeRequest.decode bytes).map fun (message, rest) => (.approveBasketTradeRequest message, rest)
  else if tag = 10631 then (ApproveReverseTesTradeRequest.decode bytes).map fun (message, rest) => (.approveReverseTesTradeRequest message, rest)
  else if tag = 10603 then (ApproveTesTradeRequest.decode bytes).map fun (message, rest) => (.approveTesTradeRequest message, rest)
  else if tag = 10118 then (CrossRequest.decode bytes).map fun (message, rest) => (.crossRequest message, rest)
  else if tag = 10120 then (DeleteAllOrderRequest.decode bytes).map fun (message, rest) => (.deleteAllOrderRequest message, rest)
  else if tag = 10408 then (DeleteAllQuoteRequest.decode bytes).map fun (message, rest) => (.deleteAllQuoteRequest message, rest)
  else if tag = 10622 then (DeleteBasketTradeRequest.decode bytes).map fun (message, rest) => (.deleteBasketTradeRequest message, rest)
  else if tag = 10132 then (DeleteClipRequest.decode bytes).map fun (message, rest) => (.deleteClipRequest message, rest)
  else if tag = 10123 then (DeleteOrderComplexRequest.decode bytes).map fun (message, rest) => (.deleteOrderComplexRequest message, rest)
  else if tag = 10142 then (DeleteOrderRequest.decode bytes).map fun (message, rest) => (.deleteOrderRequest message, rest)
  else if tag = 10109 then (DeleteOrderSingleRequest.decode bytes).map fun (message, rest) => (.deleteOrderSingleRequest message, rest)
  else if tag = 10602 then (DeleteTesTradeRequest.decode bytes).map fun (message, rest) => (.deleteTesTradeRequest message, rest)
  else if tag = 10620 then (EnterBasketTradeRequest.decode bytes).map fun (message, rest) => (.enterBasketTradeRequest message, rest)
  else if tag = 10131 then (EnterClipRequest.decode bytes).map fun (message, rest) => (.enterClipRequest message, rest)
  else if tag = 10600 then (EnterTesTradeRequest.decode bytes).map fun (message, rest) => (.enterTesTradeRequest message, rest)
  else if tag = 10011 then (Heartbeat.decode bytes).map fun (message, rest) => (.heartbeat message, rest)
  else if tag = 10040 then (InquireEnrichmentRuleIdListRequest.decode bytes).map fun (message, rest) => (.inquireEnrichmentRuleIdListRequest message, rest)
  else if tag = 10305 then (InquireMmParameterRequest.decode bytes).map fun (message, rest) => (.inquireMmParameterRequest message, rest)
  else if tag = 10323 then (InquireMarginBasedRiskLimitRequest.decode bytes).map fun (message, rest) => (.inquireMarginBasedRiskLimitRequest message, rest)
  else if tag = 10311 then (InquirePreTradeRiskLimitsRequest.decode bytes).map fun (message, rest) => (.inquirePreTradeRiskLimitsRequest message, rest)
  else if tag = 10035 then (InquireSessionListRequest.decode bytes).map fun (message, rest) => (.inquireSessionListRequest message, rest)
  else if tag = 10038 then (InquireUserRequest.decode bytes).map fun (message, rest) => (.inquireUserRequest message, rest)
  else if tag = 10000 then (LogonRequest.decode bytes).map fun (message, rest) => (.logonRequest message, rest)
  else if tag = 19000 then (LogonRequestEncrypted.decode bytes).map fun (message, rest) => (.logonRequestEncrypted message, rest)
  else if tag = 10002 then (LogoutRequest.decode bytes).map fun (message, rest) => (.logoutRequest message, rest)
  else if tag = 10303 then (MmParameterDefinitionRequest.decode bytes).map fun (message, rest) => (.mmParameterDefinitionRequest message, rest)
  else if tag = 10115 then (MassOrder.decode bytes).map fun (message, rest) => (.massOrder message, rest)
  else if tag = 10405 then (MassQuoteRequest.decode bytes).map fun (message, rest) => (.massQuoteRequest message, rest)
  else if tag = 10621 then (ModifyBasketTradeRequest.decode bytes).map fun (message, rest) => (.modifyBasketTradeRequest message, rest)
  else if tag = 10114 then (ModifyOrderComplexRequest.decode bytes).map fun (message, rest) => (.modifyOrderComplexRequest message, rest)
  else if tag = 10130 then (ModifyOrderComplexShortRequest.decode bytes).map fun (message, rest) => (.modifyOrderComplexShortRequest message, rest)
  else if tag = 10140 then (ModifyOrderRequest.decode bytes).map fun (message, rest) => (.modifyOrderRequest message, rest)
  else if tag = 10141 then (ModifyOrderShortRequest.decode bytes).map fun (message, rest) => (.modifyOrderShortRequest message, rest)
  else if tag = 10106 then (ModifyOrderSingleRequest.decode bytes).map fun (message, rest) => (.modifyOrderSingleRequest message, rest)
  else if tag = 10126 then (ModifyOrderSingleShortRequest.decode bytes).map fun (message, rest) => (.modifyOrderSingleShortRequest message, rest)
  else if tag = 10601 then (ModifyTesTradeRequest.decode bytes).map fun (message, rest) => (.modifyTesTradeRequest message, rest)
  else if tag = 10113 then (NewOrderComplexRequest.decode bytes).map fun (message, rest) => (.newOrderComplexRequest message, rest)
  else if tag = 10129 then (NewOrderComplexShortRequest.decode bytes).map fun (message, rest) => (.newOrderComplexShortRequest message, rest)
  else if tag = 10138 then (NewOrderRequest.decode bytes).map fun (message, rest) => (.newOrderRequest message, rest)
  else if tag = 10139 then (NewOrderShortRequest.decode bytes).map fun (message, rest) => (.newOrderShortRequest message, rest)
  else if tag = 10100 then (NewOrderSingleRequest.decode bytes).map fun (message, rest) => (.newOrderSingleRequest message, rest)
  else if tag = 10125 then (NewOrderSingleShortRequest.decode bytes).map fun (message, rest) => (.newOrderSingleShortRequest message, rest)
  else if tag = 10320 then (PingRequest.decode bytes).map fun (message, rest) => (.pingRequest message, rest)
  else if tag = 10312 then (PreTradeRiskLimitsDefinitionRequest.decode bytes).map fun (message, rest) => (.preTradeRiskLimitsDefinitionRequest message, rest)
  else if tag = 10403 then (QuoteActivationRequest.decode bytes).map fun (message, rest) => (.quoteActivationRequest message, rest)
  else if tag = 10401 then (RfqRequest.decode bytes).map fun (message, rest) => (.rfqRequest message, rest)
  else if tag = 10026 then (RetransmitMeMessageRequest.decode bytes).map fun (message, rest) => (.retransmitMeMessageRequest message, rest)
  else if tag = 10008 then (RetransmitRequest.decode bytes).map fun (message, rest) => (.retransmitRequest message, rest)
  else if tag = 10630 then (ReverseTesTradeRequest.decode bytes).map fun (message, rest) => (.reverseTesTradeRequest message, rest)
  else if tag = 10702 then (SrqsEnterQuoteRequest.decode bytes).map fun (message, rest) => (.srqsEnterQuoteRequest message, rest)
  else if tag = 10704 then (SrqsHitQuoteRequest.decode bytes).map fun (message, rest) => (.srqsHitQuoteRequest message, rest)
  else if tag = 10718 then (SrqsInquireSmartRespondentRequest.decode bytes).map fun (message, rest) => (.srqsInquireSmartRespondentRequest message, rest)
  else if tag = 10700 then (SrqsOpenNegotiationRequest.decode bytes).map fun (message, rest) => (.srqsOpenNegotiationRequest message, rest)
  else if tag = 10720 then (SrqsQuoteSnapshotRequest.decode bytes).map fun (message, rest) => (.srqsQuoteSnapshotRequest message, rest)
  else if tag = 10717 then (SrqsQuotingStatusRequest.decode bytes).map fun (message, rest) => (.srqsQuotingStatusRequest message, rest)
  else if tag = 10706 then (SrqsUpdateDealStatusRequest.decode bytes).map fun (message, rest) => (.srqsUpdateDealStatusRequest message, rest)
  else if tag = 10701 then (SrqsUpdateNegotiationRequest.decode bytes).map fun (message, rest) => (.srqsUpdateNegotiationRequest message, rest)
  else if tag = 10025 then (SubscribeRequest.decode bytes).map fun (message, rest) => (.subscribeRequest message, rest)
  else if tag = 10006 then (UnsubscribeRequest.decode bytes).map fun (message, rest) => (.unsubscribeRequest message, rest)
  else if tag = 10325 then (UpdateRemainingRiskAllowanceBaseRequest.decode bytes).map fun (message, rest) => (.updateRemainingRiskAllowanceBaseRequest message, rest)
  else if tag = 10612 then (UploadTesTradeRequest.decode bytes).map fun (message, rest) => (.uploadTesTradeRequest message, rest)
  else if tag = 10018 then (UserLoginRequest.decode bytes).map fun (message, rest) => (.userLoginRequest message, rest)
  else if tag = 19018 then (UserLoginRequestEncrypted.decode bytes).map fun (message, rest) => (.userLoginRequestEncrypted message, rest)
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
  | addComplexInstrumentRequest inner =>
    have bound_inner := AddComplexInstrumentRequest.encode_length_le inner
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | addFlexibleInstrumentRequest inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length, AddFlexibleInstrumentRequest.encode_length]
    omega
  | addScaledSimpleInstrumentRequest inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length, AddScaledSimpleInstrumentRequest.encode_length]
    omega
  | amendBasketTradeRequest inner =>
    have bound_inner := AmendBasketTradeRequest.encode_length_le inner
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | approveBasketTradeRequest inner =>
    have bound_inner := ApproveBasketTradeRequest.encode_length_le inner
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | approveReverseTesTradeRequest inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length, ApproveReverseTesTradeRequest.encode_length]
    omega
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
  | deleteBasketTradeRequest inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length, DeleteBasketTradeRequest.encode_length]
    omega
  | deleteClipRequest inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length, DeleteClipRequest.encode_length]
    omega
  | deleteOrderComplexRequest inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length, DeleteOrderComplexRequest.encode_length]
    omega
  | deleteOrderRequest inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length, DeleteOrderRequest.encode_length]
    omega
  | deleteOrderSingleRequest inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length, DeleteOrderSingleRequest.encode_length]
    omega
  | deleteTesTradeRequest inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length, DeleteTesTradeRequest.encode_length]
    omega
  | enterBasketTradeRequest inner =>
    have bound_inner := EnterBasketTradeRequest.encode_length_le inner
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | enterClipRequest inner =>
    have bound_inner := EnterClipRequest.encode_length_le inner
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length]
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
  | inquireMmParameterRequest inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length, InquireMmParameterRequest.encode_length]
    omega
  | inquireMarginBasedRiskLimitRequest inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length, InquireMarginBasedRiskLimitRequest.encode_length]
    omega
  | inquirePreTradeRiskLimitsRequest inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length, InquirePreTradeRiskLimitsRequest.encode_length]
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
  | logonRequestEncrypted inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length, LogonRequestEncrypted.encode_length]
    omega
  | logoutRequest inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length, LogoutRequest.encode_length]
    omega
  | mmParameterDefinitionRequest inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length, MmParameterDefinitionRequest.encode_length]
    omega
  | massOrder inner =>
    have bound_inner := MassOrder.encode_length_le inner
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | massQuoteRequest inner =>
    have bound_inner := MassQuoteRequest.encode_length_le inner
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | modifyBasketTradeRequest inner =>
    have bound_inner := ModifyBasketTradeRequest.encode_length_le inner
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | modifyOrderComplexRequest inner =>
    have bound_inner := ModifyOrderComplexRequest.encode_length_le inner
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | modifyOrderComplexShortRequest inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length, ModifyOrderComplexShortRequest.encode_length]
    omega
  | modifyOrderRequest inner =>
    have bound_inner := ModifyOrderRequest.encode_length_le inner
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | modifyOrderShortRequest inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length, ModifyOrderShortRequest.encode_length]
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
  | newOrderComplexRequest inner =>
    have bound_inner := NewOrderComplexRequest.encode_length_le inner
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | newOrderComplexShortRequest inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length, NewOrderComplexShortRequest.encode_length]
    omega
  | newOrderRequest inner =>
    have bound_inner := NewOrderRequest.encode_length_le inner
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | newOrderShortRequest inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length, NewOrderShortRequest.encode_length]
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
  | preTradeRiskLimitsDefinitionRequest inner =>
    have bound_inner := PreTradeRiskLimitsDefinitionRequest.encode_length_le inner
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length]
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
  | reverseTesTradeRequest inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length, ReverseTesTradeRequest.encode_length]
    omega
  | srqsEnterQuoteRequest inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length, SrqsEnterQuoteRequest.encode_length]
    omega
  | srqsHitQuoteRequest inner =>
    have bound_inner := SrqsHitQuoteRequest.encode_length_le inner
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | srqsInquireSmartRespondentRequest inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length, SrqsInquireSmartRespondentRequest.encode_length]
    omega
  | srqsOpenNegotiationRequest inner =>
    have bound_inner := SrqsOpenNegotiationRequest.encode_length_le inner
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | srqsQuoteSnapshotRequest inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length, SrqsQuoteSnapshotRequest.encode_length]
    omega
  | srqsQuotingStatusRequest inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length, SrqsQuotingStatusRequest.encode_length]
    omega
  | srqsUpdateDealStatusRequest inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length, SrqsUpdateDealStatusRequest.encode_length]
    omega
  | srqsUpdateNegotiationRequest inner =>
    have bound_inner := SrqsUpdateNegotiationRequest.encode_length_le inner
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | subscribeRequest inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length, SubscribeRequest.encode_length]
    omega
  | unsubscribeRequest inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length, UnsubscribeRequest.encode_length]
    omega
  | updateRemainingRiskAllowanceBaseRequest inner =>
    have bound_inner := UpdateRemainingRiskAllowanceBaseRequest.encode_length_le inner
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | uploadTesTradeRequest inner =>
    have bound_inner := UploadTesTradeRequest.encode_length_le inner
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | userLoginRequest inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length, UserLoginRequest.encode_length]
    omega
  | userLoginRequestEncrypted inner =>
    simp only [ClientPayload.encode, List.length_append, encodeUIntLE_length, UserLoginRequestEncrypted.encode_length]
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

end Omi.EurexT7EtiFbeV121Client
