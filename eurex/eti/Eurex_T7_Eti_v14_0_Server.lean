import Omi.Wire

/-!
# Eurex Exchange Enhanced Trading Interface v14.0

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Add Complex Instrument Response is not framed: its length Body Len is not the integer that leads it.

Note: Add Flexible Instrument Response is not framed: its length Body Len is not the integer that leads it.

Note: Add Scaled Simple Instrument Response is not framed: its length Body Len is not the integer that leads it.

Note: Basket Approve Broadcast is not framed: its length Body Len is not the integer that leads it.

Note: Basket Broadcast is not framed: its length Body Len is not the integer that leads it.

Note: Basket Delete Broadcast is not framed: its length Body Len is not the integer that leads it.

Note: Basket Execution Broadcast is not framed: its length Body Len is not the integer that leads it.

Note: Basket Response is not framed: its length Body Len is not the integer that leads it.

Note: Basket Roll Broadcast is not framed: its length Body Len is not the integer that leads it.

Note: Broadcast Error Notification is not framed: its length Body Len is not the integer that leads it.

Note: Clip Deletion Notification is not framed: its length Body Len is not the integer that leads it.

Note: Clip Execution Notification is not framed: its length Body Len is not the integer that leads it.

Note: Clip Response is not framed: its length Body Len is not the integer that leads it.

Note: Cross Request Response is not framed: its length Body Len is not the integer that leads it.

Note: Delete All Order Broadcast is not framed: its length Body Len is not the integer that leads it.

Note: Delete All Order Nr Response is not framed: its length Body Len is not the integer that leads it.

Note: Delete All Order Quote Event Broadcast is not framed: its length Body Len is not the integer that leads it.

Note: Delete All Order Response is not framed: its length Body Len is not the integer that leads it.

Note: Delete All Quote Broadcast is not framed: its length Body Len is not the integer that leads it.

Note: Delete All Quote Response is not framed: its length Body Len is not the integer that leads it.

Note: Delete Order Broadcast is not framed: its length Body Len is not the integer that leads it.

Note: Delete Order Nr Response is not framed: its length Body Len is not the integer that leads it.

Note: Delete Order Response is not framed: its length Body Len is not the integer that leads it.

Note: Forced Logout Notification is not framed: its length Body Len is not the integer that leads it.

Note: Forced User Logout Notification is not framed: its length Body Len is not the integer that leads it.

Note: Heartbeat Notification is not framed: its length Body Len is not the integer that leads it.

Note: Inquire Enrichment Rule Id List Response is not framed: its length Body Len is not the integer that leads it.

Note: Inquire Mm Parameter Response is not framed: its length Body Len is not the integer that leads it.

Note: Inquire Margin Based Risk Limit Response is not framed: its length Body Len is not the integer that leads it.

Note: Inquire Session List Response is not framed: its length Body Len is not the integer that leads it.

Note: Inquire User Response is not framed: its length Body Len is not the integer that leads it.

Note: Legal Notification Broadcast is not framed: its length Body Len is not the integer that leads it.

Note: Logon Response is not framed: its length Body Len is not the integer that leads it.

Note: Logout Response is not framed: its length Body Len is not the integer that leads it.

Note: Mm Parameter Definition Response is not framed: its length Body Len is not the integer that leads it.

Note: Mass Order Ack is not framed: its length Body Len is not the integer that leads it.

Note: Mass Quote Response is not framed: its length Body Len is not the integer that leads it.

Note: Modify Order Nr Response is not framed: its length Body Len is not the integer that leads it.

Note: Modify Order Response is not framed: its length Body Len is not the integer that leads it.

Note: New Order Nr Response is not framed: its length Body Len is not the integer that leads it.

Note: New Order Response is not framed: its length Body Len is not the integer that leads it.

Note: News Broadcast is not framed: its length Body Len is not the integer that leads it.

Note: Order Exec Notification is not framed: its length Body Len is not the integer that leads it.

Note: Order Exec Report Broadcast is not framed: its length Body Len is not the integer that leads it.

Note: Order Exec Response is not framed: its length Body Len is not the integer that leads it.

Note: Party Action Report is not framed: its length Body Len is not the integer that leads it.

Note: Party Entitlements Update Report is not framed: its length Body Len is not the integer that leads it.

Note: Ping Response is not framed: its length Body Len is not the integer that leads it.

Note: Pre Trade Risk Limit Response is not framed: its length Body Len is not the integer that leads it.

Note: Quote Activation Notification is not framed: its length Body Len is not the integer that leads it.

Note: Quote Activation Response is not framed: its length Body Len is not the integer that leads it.

Note: Quote Execution Report is not framed: its length Body Len is not the integer that leads it.

Note: Rfq Response is not framed: its length Body Len is not the integer that leads it.

Note: Reject is not framed: its length Body Len is not the integer that leads it.

Note: Retransmit Me Message Response is not framed: its length Body Len is not the integer that leads it.

Note: Retransmit Response is not framed: its length Body Len is not the integer that leads it.

Note: Risk Notification Broadcast is not framed: its length Body Len is not the integer that leads it.

Note: Srqs Create Deal Notification is not framed: its length Body Len is not the integer that leads it.

Note: Srqs Deal Notification is not framed: its length Body Len is not the integer that leads it.

Note: Srqs Deal Response is not framed: its length Body Len is not the integer that leads it.

Note: Srqs Inquire Smart Respondent Response is not framed: its length Body Len is not the integer that leads it.

Note: Srqs Negotiation Notification is not framed: its length Body Len is not the integer that leads it.

Note: Srqs Negotiation Requester Notification is not framed: its length Body Len is not the integer that leads it.

Note: Srqs Negotiation Status Notification is not framed: its length Body Len is not the integer that leads it.

Note: Srqs Open Negotiation Notification is not framed: its length Body Len is not the integer that leads it.

Note: Srqs Open Negotiation Requester Notification is not framed: its length Body Len is not the integer that leads it.

Note: Srqs Quote Notification is not framed: its length Body Len is not the integer that leads it.

Note: Srqs Quote Response is not framed: its length Body Len is not the integer that leads it.

Note: Srqs Quote Snapshot Notification is not framed: its length Body Len is not the integer that leads it.

Note: Srqs Response is not framed: its length Body Len is not the integer that leads it.

Note: Srqs Status Broadcast is not framed: its length Body Len is not the integer that leads it.

Note: Service Availability Broadcast is not framed: its length Body Len is not the integer that leads it.

Note: Service Availability Market Broadcast is not framed: its length Body Len is not the integer that leads it.

Note: Status Broadcast is not framed: its length Body Len is not the integer that leads it.

Note: Subscribe Response is not framed: its length Body Len is not the integer that leads it.

Note: Tes Approve Broadcast is not framed: its length Body Len is not the integer that leads it.

Note: Tes Broadcast is not framed: its length Body Len is not the integer that leads it.

Note: Tes Delete Broadcast is not framed: its length Body Len is not the integer that leads it.

Note: Tes Execution Broadcast is not framed: its length Body Len is not the integer that leads it.

Note: Tes Response is not framed: its length Body Len is not the integer that leads it.

Note: Tes Reversal Broadcast is not framed: its length Body Len is not the integer that leads it.

Note: Tes Trade Broadcast is not framed: its length Body Len is not the integer that leads it.

Note: Tes Trading Session Status Broadcast is not framed: its length Body Len is not the integer that leads it.

Note: Tes Upload Broadcast is not framed: its length Body Len is not the integer that leads it.

Note: Tm Trading Session Status Broadcast is not framed: its length Body Len is not the integer that leads it.

Note: Throttle Update Notification is not framed: its length Body Len is not the integer that leads it.

Note: Trade Broadcast is not framed: its length Body Len is not the integer that leads it.

Note: Trading Session Status Broadcast is not framed: its length Body Len is not the integer that leads it.

Note: Unsubscribe Response is not framed: its length Body Len is not the integer that leads it.

Note: Update Remaining Risk Allowance Base Response is not framed: its length Body Len is not the integer that leads it.

Note: User Login Response is not framed: its length Body Len is not the integer that leads it.

Note: User Logout Response is not framed: its length Body Len is not the integer that leads it.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.EurexT7EtiFbeV140Server

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

/-- Message Event Source: one byte code -/
def MessageEventSource.codes : List UInt8 :=
  [0x49, 0x41, 0x52, 0x51]

inductive MessageEventSource where
  | broadcasttoInitiator -- Broadcastto Initiator
  | broadcasttoApprover -- Broadcastto Approver
  | broadcasttoRequester -- Broadcastto Requester
  | broadcasttoQuoteSubmitter -- Broadcastto Quote Submitter
  | unlisted (byte : { byte : UInt8 // byte ∉ MessageEventSource.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MessageEventSource

def toByte : MessageEventSource → UInt8
  | .broadcasttoInitiator => 0x49
  | .broadcasttoApprover => 0x41
  | .broadcasttoRequester => 0x52
  | .broadcasttoQuoteSubmitter => 0x51
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MessageEventSource :=
  if byte = 0x49 then .broadcasttoInitiator
  else if byte = 0x41 then .broadcasttoApprover
  else if byte = 0x52 then .broadcasttoRequester
  else .broadcasttoQuoteSubmitter

def ofByte (byte : UInt8) : MessageEventSource :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MessageEventSource) : ofByte value.toByte = value := by
  cases value with
  | broadcasttoInitiator => decide
  | broadcasttoApprover => decide
  | broadcasttoRequester => decide
  | broadcasttoQuoteSubmitter => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : MessageEventSource) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (MessageEventSource × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : MessageEventSource) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : MessageEventSource) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end MessageEventSource

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

/-- Ord Status: one byte code -/
def OrdStatus.codes : List UInt8 :=
  [0x30, 0x31, 0x32, 0x34, 0x36, 0x39]

inductive OrdStatus where
  | new -- New
  | partiallyfilled -- Partiallyfilled
  | filled -- Filled
  | canceled -- Canceled
  | pendingCancel -- Pending Cancel
  | suspended -- Suspended
  | unlisted (byte : { byte : UInt8 // byte ∉ OrdStatus.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrdStatus

def toByte : OrdStatus → UInt8
  | .new => 0x30
  | .partiallyfilled => 0x31
  | .filled => 0x32
  | .canceled => 0x34
  | .pendingCancel => 0x36
  | .suspended => 0x39
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrdStatus :=
  if byte = 0x30 then .new
  else if byte = 0x31 then .partiallyfilled
  else if byte = 0x32 then .filled
  else if byte = 0x34 then .canceled
  else if byte = 0x36 then .pendingCancel
  else .suspended

def ofByte (byte : UInt8) : OrdStatus :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrdStatus) : ofByte value.toByte = value := by
  cases value with
  | new => decide
  | partiallyfilled => decide
  | filled => decide
  | canceled => decide
  | pendingCancel => decide
  | suspended => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OrdStatus) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OrdStatus × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OrdStatus) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OrdStatus) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OrdStatus

/-- Exec Type: one byte code -/
def ExecType.codes : List UInt8 :=
  [0x30, 0x34, 0x35, 0x36, 0x39, 0x44, 0x4C, 0x46]

inductive ExecType where
  | new -- New
  | canceled -- Canceled
  | replaced -- Replaced
  | pendingCancele -- Pending Cancele
  | suspended -- Suspended
  | restated -- Restated
  | triggered -- Triggered
  | trade -- Trade
  | unlisted (byte : { byte : UInt8 // byte ∉ ExecType.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ExecType

def toByte : ExecType → UInt8
  | .new => 0x30
  | .canceled => 0x34
  | .replaced => 0x35
  | .pendingCancele => 0x36
  | .suspended => 0x39
  | .restated => 0x44
  | .triggered => 0x4C
  | .trade => 0x46
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ExecType :=
  if byte = 0x30 then .new
  else if byte = 0x34 then .canceled
  else if byte = 0x35 then .replaced
  else if byte = 0x36 then .pendingCancele
  else if byte = 0x39 then .suspended
  else if byte = 0x44 then .restated
  else if byte = 0x4C then .triggered
  else .trade

def ofByte (byte : UInt8) : ExecType :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ExecType) : ofByte value.toByte = value := by
  cases value with
  | new => decide
  | canceled => decide
  | replaced => decide
  | pendingCancele => decide
  | suspended => decide
  | restated => decide
  | triggered => decide
  | trade => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ExecType) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ExecType × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ExecType) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ExecType) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ExecType

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

/-- List Update Action: one byte code -/
def ListUpdateAction.codes : List UInt8 :=
  [0x41, 0x44]

inductive ListUpdateAction where
  | add -- Add
  | delete -- Delete
  | unlisted (byte : { byte : UInt8 // byte ∉ ListUpdateAction.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace ListUpdateAction

def toByte : ListUpdateAction → UInt8
  | .add => 0x41
  | .delete => 0x44
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : ListUpdateAction :=
  if byte = 0x41 then .add
  else .delete

def ofByte (byte : UInt8) : ListUpdateAction :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : ListUpdateAction) : ofByte value.toByte = value := by
  cases value with
  | add => decide
  | delete => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : ListUpdateAction) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (ListUpdateAction × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : ListUpdateAction) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : ListUpdateAction) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end ListUpdateAction

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

/-- Order Category: one byte code -/
def OrderCategory.codes : List UInt8 :=
  [0x31, 0x32]

inductive OrderCategory where
  | order -- Order
  | quote -- Quote
  | unlisted (byte : { byte : UInt8 // byte ∉ OrderCategory.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace OrderCategory

def toByte : OrderCategory → UInt8
  | .order => 0x31
  | .quote => 0x32
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrderCategory :=
  if byte = 0x31 then .order
  else .quote

def ofByte (byte : UInt8) : OrderCategory :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : OrderCategory) : ofByte value.toByte = value := by
  cases value with
  | order => decide
  | quote => decide
  | unlisted byte => simp [ofByte, toByte, byte.property]

def encode (value : OrderCategory) : List UInt8 :=
  [value.toByte]

def decode : List UInt8 → Option (OrderCategory × List UInt8)
  | byte :: rest => some (ofByte byte, rest)
  | [] => none

@[simp] theorem encode_length (value : OrderCategory) : (encode value).length = 1 :=
  rfl

@[simp] theorem decode_encode (value : OrderCategory) (rest : List UInt8) :
    decode (encode value ++ rest) = some (value, rest) := by
  simp [decode, encode, ofByte_toByte]

end OrderCategory

/-- Nr Response Header Me Comp: 48 bytes -/
structure NrResponseHeaderMeComp where
  requestTime : BitVec 64
  trdRegTsTimeIn : BitVec 64
  trdRegTsTimeOut : BitVec 64
  responseIn : BitVec 64
  sendingTime : BitVec 64
  msgSeqNum : BitVec 32
  lastFragment : BitVec 8
  pad3 : Alpha 3
  deriving DecidableEq, Repr

namespace NrResponseHeaderMeComp

def encode (message : NrResponseHeaderMeComp) : List UInt8 :=
  encodeUIntLE 8 message.requestTime
    ++ encodeUIntLE 8 message.trdRegTsTimeIn
    ++ encodeUIntLE 8 message.trdRegTsTimeOut
    ++ encodeUIntLE 8 message.responseIn
    ++ encodeUIntLE 8 message.sendingTime
    ++ encodeUIntLE 4 message.msgSeqNum
    ++ encodeUInt 1 message.lastFragment
    ++ Alpha.encode message.pad3

def decode (bytes : List UInt8) : Option (NrResponseHeaderMeComp × List UInt8) := do
  let (requestTime, bytes) ← decodeUIntLE 8 bytes
  let (trdRegTsTimeIn, bytes) ← decodeUIntLE 8 bytes
  let (trdRegTsTimeOut, bytes) ← decodeUIntLE 8 bytes
  let (responseIn, bytes) ← decodeUIntLE 8 bytes
  let (sendingTime, bytes) ← decodeUIntLE 8 bytes
  let (msgSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (lastFragment, bytes) ← decodeUInt 1 bytes
  let (pad3, bytes) ← Alpha.decode 3 bytes
  pure ({ requestTime, trdRegTsTimeIn, trdRegTsTimeOut, responseIn, sendingTime, msgSeqNum, lastFragment, pad3 }, bytes)

@[simp] theorem encode_length (message : NrResponseHeaderMeComp) : (encode message).length = 48 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : NrResponseHeaderMeComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NrResponseHeaderMeComp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end NrResponseHeaderMeComp

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
    ++ encodeUIntLE 8 message.legPrice
    ++ encodeUIntLE 4 message.legSymbol
    ++ encodeUIntLE 4 message.legRatioQty
    ++ encodeUInt 1 message.legSide
    ++ encodeUInt 1 message.legSecurityType
    ++ Alpha.encode message.pad6

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
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end InstrmtLegGrpComp

/-- Add Complex Instrument Response -/
structure AddComplexInstrumentResponse where
  pad2 : Alpha 2
  nrResponseHeaderMeComp : NrResponseHeaderMeComp
  lowLimitPrice : BitVec 64
  highLimitPrice : BitVec 64
  relatedPx : BitVec 64
  securityId : BitVec 64
  lastUpdateTime : BitVec 64
  securityResponseId : BitVec 64
  marketSegmentId : BitVec 32
  numberOfSecurities : BitVec 32
  securitySubType : BitVec 32
  quantityScalingFactor : BitVec 16
  multilegModel : BitVec 8
  impliedMarketIndicator : BitVec 8
  productComplex : BitVec 8
  pad6 : Alpha 6
  instrmtLegGrpComp : Bounded 1 InstrmtLegGrpComp
  deriving DecidableEq, Repr

namespace AddComplexInstrumentResponse

def encode (message : AddComplexInstrumentResponse) : List UInt8 :=
  Alpha.encode message.pad2
    ++ NrResponseHeaderMeComp.encode message.nrResponseHeaderMeComp
    ++ encodeUIntLE 8 message.lowLimitPrice
    ++ encodeUIntLE 8 message.highLimitPrice
    ++ encodeUIntLE 8 message.relatedPx
    ++ encodeUIntLE 8 message.securityId
    ++ encodeUIntLE 8 message.lastUpdateTime
    ++ encodeUIntLE 8 message.securityResponseId
    ++ encodeUIntLE 4 message.marketSegmentId
    ++ encodeUIntLE 4 message.numberOfSecurities
    ++ encodeUIntLE 4 message.securitySubType
    ++ encodeUIntLE 2 message.quantityScalingFactor
    ++ encodeUInt 1 message.multilegModel
    ++ encodeUInt 1 message.impliedMarketIndicator
    ++ encodeUInt 1 message.productComplex
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.instrmtLegGrpComp.val.length)
    ++ Alpha.encode message.pad6
    ++ encodeMany InstrmtLegGrpComp.encode message.instrmtLegGrpComp.val

def decode (bytes : List UInt8) : Option (AddComplexInstrumentResponse × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (nrResponseHeaderMeComp, bytes) ← NrResponseHeaderMeComp.decode bytes
  let (lowLimitPrice, bytes) ← decodeUIntLE 8 bytes
  let (highLimitPrice, bytes) ← decodeUIntLE 8 bytes
  let (relatedPx, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (lastUpdateTime, bytes) ← decodeUIntLE 8 bytes
  let (securityResponseId, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (numberOfSecurities, bytes) ← decodeUIntLE 4 bytes
  let (securitySubType, bytes) ← decodeUIntLE 4 bytes
  let (quantityScalingFactor, bytes) ← decodeUIntLE 2 bytes
  let (multilegModel, bytes) ← decodeUInt 1 bytes
  let (impliedMarketIndicator, bytes) ← decodeUInt 1 bytes
  let (productComplex, bytes) ← decodeUInt 1 bytes
  let (noLegOnbooks, bytes) ← decodeUInt 1 bytes
  let (pad6, bytes) ← Alpha.decode 6 bytes
  let (instrmtLegGrpComp_, bytes) ← decodeMany InstrmtLegGrpComp.decode noLegOnbooks.toNat bytes
  if fits_instrmtLegGrpComp : instrmtLegGrpComp_.length < 256 ^ 1 then
    pure ({ pad2, nrResponseHeaderMeComp, lowLimitPrice, highLimitPrice, relatedPx, securityId, lastUpdateTime, securityResponseId, marketSegmentId, numberOfSecurities, securitySubType, quantityScalingFactor, multilegModel, impliedMarketIndicator, productComplex, pad6, instrmtLegGrpComp := ⟨instrmtLegGrpComp_, fits_instrmtLegGrpComp⟩ }, bytes)
  else none

theorem encode_length_pos (message : AddComplexInstrumentResponse) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : AddComplexInstrumentResponse) : (encode message).length ≤ 8282 := by
  have bound_instrmtLegGrpComp := message.instrmtLegGrpComp.length_lt
  unfold encode
  simp only [List.length_append, Alpha.encode_length, NrResponseHeaderMeComp.encode_length, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const InstrmtLegGrpComp.encode 32 InstrmtLegGrpComp.encode_length]
  omega

@[simp] theorem decode_encode (message : AddComplexInstrumentResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [NrResponseHeaderMeComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 InstrmtLegGrpComp.encode InstrmtLegGrpComp.decode InstrmtLegGrpComp.decode_encode]
  simp only [Option.bind_some]
  simp only [message.instrmtLegGrpComp.length_lt, ↓reduceDIte]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : AddComplexInstrumentResponse) : decode (encode message) = some (message, []) := by
  have trailing := decode_encode message []
  rw [List.append_nil] at trailing
  exact trailing

end AddComplexInstrumentResponse

/-- Add Flexible Instrument Response: 98 bytes -/
structure AddFlexibleInstrumentResponse where
  pad2 : Alpha 2
  nrResponseHeaderMeComp : NrResponseHeaderMeComp
  securityResponseId : BitVec 64
  securityId : BitVec 64
  strikePrice : BitVec 64
  marketSegmentId : BitVec 32
  maturityDate : BitVec 32
  contractDate : BitVec 32
  productComplex : BitVec 8
  settlMethod : SettlMethod
  optAttribute : BitVec 8
  putOrCall : BitVec 8
  exerciseStyle : BitVec 8
  pad7 : Alpha 7
  deriving DecidableEq, Repr

namespace AddFlexibleInstrumentResponse

def encode (message : AddFlexibleInstrumentResponse) : List UInt8 :=
  Alpha.encode message.pad2
    ++ NrResponseHeaderMeComp.encode message.nrResponseHeaderMeComp
    ++ encodeUIntLE 8 message.securityResponseId
    ++ encodeUIntLE 8 message.securityId
    ++ encodeUIntLE 8 message.strikePrice
    ++ encodeUIntLE 4 message.marketSegmentId
    ++ encodeUIntLE 4 message.maturityDate
    ++ encodeUIntLE 4 message.contractDate
    ++ encodeUInt 1 message.productComplex
    ++ SettlMethod.encode message.settlMethod
    ++ encodeUInt 1 message.optAttribute
    ++ encodeUInt 1 message.putOrCall
    ++ encodeUInt 1 message.exerciseStyle
    ++ Alpha.encode message.pad7

def decode (bytes : List UInt8) : Option (AddFlexibleInstrumentResponse × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (nrResponseHeaderMeComp, bytes) ← NrResponseHeaderMeComp.decode bytes
  let (securityResponseId, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (strikePrice, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (maturityDate, bytes) ← decodeUIntLE 4 bytes
  let (contractDate, bytes) ← decodeUIntLE 4 bytes
  let (productComplex, bytes) ← decodeUInt 1 bytes
  let (settlMethod, bytes) ← SettlMethod.decode bytes
  let (optAttribute, bytes) ← decodeUInt 1 bytes
  let (putOrCall, bytes) ← decodeUInt 1 bytes
  let (exerciseStyle, bytes) ← decodeUInt 1 bytes
  let (pad7, bytes) ← Alpha.decode 7 bytes
  pure ({ pad2, nrResponseHeaderMeComp, securityResponseId, securityId, strikePrice, marketSegmentId, maturityDate, contractDate, productComplex, settlMethod, optAttribute, putOrCall, exerciseStyle, pad7 }, bytes)

@[simp] theorem encode_length (message : AddFlexibleInstrumentResponse) : (encode message).length = 98 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, NrResponseHeaderMeComp.encode_length, encodeUIntLE_length, encodeUInt_length, SettlMethod.encode_length]

theorem encode_length_pos (message : AddFlexibleInstrumentResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AddFlexibleInstrumentResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [NrResponseHeaderMeComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [SettlMethod.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : AddFlexibleInstrumentResponse) : decode (encode message) = some (message, []) := by
  have trailing := decode_encode message []
  rw [List.append_nil] at trailing
  exact trailing

end AddFlexibleInstrumentResponse

/-- Add Scaled Simple Instrument Response: 98 bytes -/
structure AddScaledSimpleInstrumentResponse where
  pad2 : Alpha 2
  nrResponseHeaderMeComp : NrResponseHeaderMeComp
  relatedSecurityId : BitVec 64
  securityId : BitVec 64
  lastUpdateTime : BitVec 64
  securityResponseId : BitVec 64
  marketSegmentId : BitVec 32
  quantityScalingFactor : BitVec 16
  multilegModel : BitVec 8
  impliedMarketIndicator : BitVec 8
  productComplex : BitVec 8
  pad7 : Alpha 7
  deriving DecidableEq, Repr

namespace AddScaledSimpleInstrumentResponse

def encode (message : AddScaledSimpleInstrumentResponse) : List UInt8 :=
  Alpha.encode message.pad2
    ++ NrResponseHeaderMeComp.encode message.nrResponseHeaderMeComp
    ++ encodeUIntLE 8 message.relatedSecurityId
    ++ encodeUIntLE 8 message.securityId
    ++ encodeUIntLE 8 message.lastUpdateTime
    ++ encodeUIntLE 8 message.securityResponseId
    ++ encodeUIntLE 4 message.marketSegmentId
    ++ encodeUIntLE 2 message.quantityScalingFactor
    ++ encodeUInt 1 message.multilegModel
    ++ encodeUInt 1 message.impliedMarketIndicator
    ++ encodeUInt 1 message.productComplex
    ++ Alpha.encode message.pad7

def decode (bytes : List UInt8) : Option (AddScaledSimpleInstrumentResponse × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (nrResponseHeaderMeComp, bytes) ← NrResponseHeaderMeComp.decode bytes
  let (relatedSecurityId, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (lastUpdateTime, bytes) ← decodeUIntLE 8 bytes
  let (securityResponseId, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (quantityScalingFactor, bytes) ← decodeUIntLE 2 bytes
  let (multilegModel, bytes) ← decodeUInt 1 bytes
  let (impliedMarketIndicator, bytes) ← decodeUInt 1 bytes
  let (productComplex, bytes) ← decodeUInt 1 bytes
  let (pad7, bytes) ← Alpha.decode 7 bytes
  pure ({ pad2, nrResponseHeaderMeComp, relatedSecurityId, securityId, lastUpdateTime, securityResponseId, marketSegmentId, quantityScalingFactor, multilegModel, impliedMarketIndicator, productComplex, pad7 }, bytes)

@[simp] theorem encode_length (message : AddScaledSimpleInstrumentResponse) : (encode message).length = 98 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, NrResponseHeaderMeComp.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : AddScaledSimpleInstrumentResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AddScaledSimpleInstrumentResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [NrResponseHeaderMeComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : AddScaledSimpleInstrumentResponse) : decode (encode message) = some (message, []) := by
  have trailing := decode_encode message []
  rw [List.append_nil] at trailing
  exact trailing

end AddScaledSimpleInstrumentResponse

/-- Rbc Header Comp: 32 bytes -/
structure RbcHeaderComp where
  sendingTime : BitVec 64
  applSeqNum : BitVec 64
  applSubId : BitVec 32
  partitionId : BitVec 16
  applResendFlag : BitVec 8
  applId : BitVec 8
  lastFragment : BitVec 8
  pad7 : Alpha 7
  deriving DecidableEq, Repr

namespace RbcHeaderComp

def encode (message : RbcHeaderComp) : List UInt8 :=
  encodeUIntLE 8 message.sendingTime
    ++ encodeUIntLE 8 message.applSeqNum
    ++ encodeUIntLE 4 message.applSubId
    ++ encodeUIntLE 2 message.partitionId
    ++ encodeUInt 1 message.applResendFlag
    ++ encodeUInt 1 message.applId
    ++ encodeUInt 1 message.lastFragment
    ++ Alpha.encode message.pad7

def decode (bytes : List UInt8) : Option (RbcHeaderComp × List UInt8) := do
  let (sendingTime, bytes) ← decodeUIntLE 8 bytes
  let (applSeqNum, bytes) ← decodeUIntLE 8 bytes
  let (applSubId, bytes) ← decodeUIntLE 4 bytes
  let (partitionId, bytes) ← decodeUIntLE 2 bytes
  let (applResendFlag, bytes) ← decodeUInt 1 bytes
  let (applId, bytes) ← decodeUInt 1 bytes
  let (lastFragment, bytes) ← decodeUInt 1 bytes
  let (pad7, bytes) ← Alpha.decode 7 bytes
  pure ({ sendingTime, applSeqNum, applSubId, partitionId, applResendFlag, applId, lastFragment, pad7 }, bytes)

@[simp] theorem encode_length (message : RbcHeaderComp) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : RbcHeaderComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RbcHeaderComp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end RbcHeaderComp

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
    ++ Alpha.encode message.rootPartyContraFirm
    ++ Alpha.encode message.rootPartyContraTrader
    ++ Alpha.encode message.basketSideTradeReportId
    ++ Alpha.encode message.pad7

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
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end BasketRootPartyGrpComp

/-- Basket Side Alloc Ext Bc Grp Comp: 192 bytes -/
structure BasketSideAllocExtBcGrpComp where
  allocQty : BitVec 64
  securityId : BitVec 64
  lastPx : BitVec 64
  transBkdTime : BitVec 64
  relatedClosePrice : BitVec 64
  packageId : BitVec 32
  sideMarketSegmentId : BitVec 32
  allocId : BitVec 32
  sideTrdSubTyp : BitVec 16
  partySubIdType : BitVec 16
  side : BitVec 8
  positionEffect : PositionEffect
  effectOnBasket : BitVec 8
  tradingCapacity : BitVec 8
  tradeAllocStatus : BitVec 8
  productComplex : BitVec 8
  tradePublishIndicator : BitVec 8
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
  pad4 : Alpha 4
  deriving DecidableEq, Repr

namespace BasketSideAllocExtBcGrpComp

def encode (message : BasketSideAllocExtBcGrpComp) : List UInt8 :=
  encodeUIntLE 8 message.allocQty
    ++ encodeUIntLE 8 message.securityId
    ++ encodeUIntLE 8 message.lastPx
    ++ encodeUIntLE 8 message.transBkdTime
    ++ encodeUIntLE 8 message.relatedClosePrice
    ++ encodeUIntLE 4 message.packageId
    ++ encodeUIntLE 4 message.sideMarketSegmentId
    ++ encodeUIntLE 4 message.allocId
    ++ encodeUIntLE 2 message.sideTrdSubTyp
    ++ encodeUIntLE 2 message.partySubIdType
    ++ encodeUInt 1 message.side
    ++ PositionEffect.encode message.positionEffect
    ++ encodeUInt 1 message.effectOnBasket
    ++ encodeUInt 1 message.tradingCapacity
    ++ encodeUInt 1 message.tradeAllocStatus
    ++ encodeUInt 1 message.productComplex
    ++ encodeUInt 1 message.tradePublishIndicator
    ++ Alpha.encode message.partyExecutingFirm
    ++ Alpha.encode message.partyExecutingTrader
    ++ Alpha.encode message.account
    ++ Alpha.encode message.freeText1
    ++ Alpha.encode message.freeText2
    ++ Alpha.encode message.freeText3
    ++ Alpha.encode message.partyIdTakeUpTradingFirm
    ++ Alpha.encode message.partyIdOrderOriginationFirm
    ++ Alpha.encode message.partyIdBeneficiary
    ++ Alpha.encode message.partyIdPositionAccount
    ++ Alpha.encode message.partyIdLocationId
    ++ CustOrderHandlingInst.encode message.custOrderHandlingInst
    ++ Alpha.encode message.complianceText
    ++ Alpha.encode message.pad4

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (BasketSideAllocExtBcGrpComp × List UInt8) := do
  let (allocQty, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  let (transBkdTime, bytes) ← decodeUIntLE 8 bytes
  let (relatedClosePrice, bytes) ← decodeUIntLE 8 bytes
  let (packageId, bytes) ← decodeUIntLE 4 bytes
  let (sideMarketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (allocId, bytes) ← decodeUIntLE 4 bytes
  let (sideTrdSubTyp, bytes) ← decodeUIntLE 2 bytes
  let (partySubIdType, bytes) ← decodeUIntLE 2 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (positionEffect, bytes) ← PositionEffect.decode bytes
  let (effectOnBasket, bytes) ← decodeUInt 1 bytes
  let (tradingCapacity, bytes) ← decodeUInt 1 bytes
  let (tradeAllocStatus, bytes) ← decodeUInt 1 bytes
  let (productComplex, bytes) ← decodeUInt 1 bytes
  let (tradePublishIndicator, bytes) ← decodeUInt 1 bytes
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
  let (pad4, bytes) ← Alpha.decode 4 bytes
  pure ({ allocQty, securityId, lastPx, transBkdTime, relatedClosePrice, packageId, sideMarketSegmentId, allocId, sideTrdSubTyp, partySubIdType, side, positionEffect, effectOnBasket, tradingCapacity, tradeAllocStatus, productComplex, tradePublishIndicator, partyExecutingFirm, partyExecutingTrader, account, freeText1, freeText2, freeText3, partyIdTakeUpTradingFirm, partyIdOrderOriginationFirm, partyIdBeneficiary, partyIdPositionAccount, partyIdLocationId, custOrderHandlingInst, complianceText, pad4 }, bytes)

@[simp] theorem encode_length (message : BasketSideAllocExtBcGrpComp) : (encode message).length = 192 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, PositionEffect.encode_length, Alpha.encode_length, CustOrderHandlingInst.encode_length]

theorem encode_length_pos (message : BasketSideAllocExtBcGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BasketSideAllocExtBcGrpComp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [PositionEffect.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [CustOrderHandlingInst.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end BasketSideAllocExtBcGrpComp

/-- Basket Approve Broadcast -/
structure BasketApproveBroadcast where
  pad2 : Alpha 2
  rbcHeaderComp : RbcHeaderComp
  basketTrdMatchId : BitVec 64
  origBasketTrdMatchId : BitVec 64
  transactTime : BitVec 64
  basketExecId : BitVec 32
  marketSegmentId : BitVec 32
  basketProfileId : BitVec 32
  trdType : BitVec 16
  tradeReportType : BitVec 8
  basketTradeReportType : BitVec 8
  optionalEarlyTerminationIndicator : BitVec 8
  messageEventSource : MessageEventSource
  partyIdEnteringFirm : BitVec 8
  partyEnteringTrader : Alpha 6
  basketTradeReportText : Alpha 20
  tradeReportId : Alpha 20
  pad4 : Alpha 4
  basketRootPartyGrpComp : Bounded 1 BasketRootPartyGrpComp
  basketSideAllocExtBcGrpComp : Bounded 2 BasketSideAllocExtBcGrpComp
  deriving DecidableEq, Repr

namespace BasketApproveBroadcast

def encode (message : BasketApproveBroadcast) : List UInt8 :=
  Alpha.encode message.pad2
    ++ RbcHeaderComp.encode message.rbcHeaderComp
    ++ encodeUIntLE 8 message.basketTrdMatchId
    ++ encodeUIntLE 8 message.origBasketTrdMatchId
    ++ encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 4 message.basketExecId
    ++ encodeUIntLE 4 message.marketSegmentId
    ++ encodeUIntLE 4 message.basketProfileId
    ++ encodeUIntLE 2 message.trdType
    ++ encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.basketSideAllocExtBcGrpComp.val.length)
    ++ encodeUInt 1 message.tradeReportType
    ++ encodeUInt 1 message.basketTradeReportType
    ++ encodeUInt 1 message.optionalEarlyTerminationIndicator
    ++ MessageEventSource.encode message.messageEventSource
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.basketRootPartyGrpComp.val.length)
    ++ encodeUInt 1 message.partyIdEnteringFirm
    ++ Alpha.encode message.partyEnteringTrader
    ++ Alpha.encode message.basketTradeReportText
    ++ Alpha.encode message.tradeReportId
    ++ Alpha.encode message.pad4
    ++ encodeMany BasketRootPartyGrpComp.encode message.basketRootPartyGrpComp.val
    ++ encodeMany BasketSideAllocExtBcGrpComp.encode message.basketSideAllocExtBcGrpComp.val

def decode (bytes : List UInt8) : Option (BasketApproveBroadcast × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderComp, bytes) ← RbcHeaderComp.decode bytes
  let (basketTrdMatchId, bytes) ← decodeUIntLE 8 bytes
  let (origBasketTrdMatchId, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (basketExecId, bytes) ← decodeUIntLE 4 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (basketProfileId, bytes) ← decodeUIntLE 4 bytes
  let (trdType, bytes) ← decodeUIntLE 2 bytes
  let (noBasketSideAlloc, bytes) ← decodeUIntLE 2 bytes
  let (tradeReportType, bytes) ← decodeUInt 1 bytes
  let (basketTradeReportType, bytes) ← decodeUInt 1 bytes
  let (optionalEarlyTerminationIndicator, bytes) ← decodeUInt 1 bytes
  let (messageEventSource, bytes) ← MessageEventSource.decode bytes
  let (noBasketRootPartyGrps, bytes) ← decodeUInt 1 bytes
  let (partyIdEnteringFirm, bytes) ← decodeUInt 1 bytes
  let (partyEnteringTrader, bytes) ← Alpha.decode 6 bytes
  let (basketTradeReportText, bytes) ← Alpha.decode 20 bytes
  let (tradeReportId, bytes) ← Alpha.decode 20 bytes
  let (pad4, bytes) ← Alpha.decode 4 bytes
  let (basketRootPartyGrpComp_, bytes) ← decodeMany BasketRootPartyGrpComp.decode noBasketRootPartyGrps.toNat bytes
  let (basketSideAllocExtBcGrpComp_, bytes) ← decodeMany BasketSideAllocExtBcGrpComp.decode noBasketSideAlloc.toNat bytes
  if fits_basketRootPartyGrpComp : basketRootPartyGrpComp_.length < 256 ^ 1 then
    if fits_basketSideAllocExtBcGrpComp : basketSideAllocExtBcGrpComp_.length < 256 ^ 2 then
      pure ({ pad2, rbcHeaderComp, basketTrdMatchId, origBasketTrdMatchId, transactTime, basketExecId, marketSegmentId, basketProfileId, trdType, tradeReportType, basketTradeReportType, optionalEarlyTerminationIndicator, messageEventSource, partyIdEnteringFirm, partyEnteringTrader, basketTradeReportText, tradeReportId, pad4, basketRootPartyGrpComp := ⟨basketRootPartyGrpComp_, fits_basketRootPartyGrpComp⟩, basketSideAllocExtBcGrpComp := ⟨basketSideAllocExtBcGrpComp_, fits_basketSideAllocExtBcGrpComp⟩ }, bytes)
    else none
  else none

theorem encode_length_pos (message : BasketApproveBroadcast) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : BasketApproveBroadcast) : (encode message).length ≤ 12593050 := by
  have bound_basketRootPartyGrpComp := message.basketRootPartyGrpComp.length_lt
  have bound_basketSideAllocExtBcGrpComp := message.basketSideAllocExtBcGrpComp.length_lt
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RbcHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length, MessageEventSource.encode_length, encodeMany_length_const BasketRootPartyGrpComp.encode 40 BasketRootPartyGrpComp.encode_length, encodeMany_length_const BasketSideAllocExtBcGrpComp.encode 192 BasketSideAllocExtBcGrpComp.encode_length]
  omega

@[simp] theorem decode_encode (message : BasketApproveBroadcast) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [RbcHeaderComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [MessageEventSource.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 BasketRootPartyGrpComp.encode BasketRootPartyGrpComp.decode BasketRootPartyGrpComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 2 BasketSideAllocExtBcGrpComp.encode BasketSideAllocExtBcGrpComp.decode BasketSideAllocExtBcGrpComp.decode_encode]
  simp only [Option.bind_some]
  simp only [message.basketRootPartyGrpComp.length_lt, message.basketSideAllocExtBcGrpComp.length_lt, ↓reduceDIte]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : BasketApproveBroadcast) : decode (encode message) = some (message, []) := by
  have trailing := decode_encode message []
  rw [List.append_nil] at trailing
  exact trailing

end BasketApproveBroadcast

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
    ++ encodeUIntLE 8 message.lastPx
    ++ encodeUIntLE 8 message.transBkdTime
    ++ encodeUIntLE 8 message.relatedClosePrice
    ++ encodeUIntLE 8 message.clearingTradePrice
    ++ encodeUIntLE 4 message.packageId
    ++ encodeUIntLE 4 message.sideMarketSegmentId
    ++ encodeUIntLE 2 message.sideTrdSubTyp
    ++ encodeUInt 1 message.productComplex
    ++ encodeUInt 1 message.tradePublishIndicator
    ++ encodeUInt 1 message.instrmtMatchSideId
    ++ encodeUInt 1 message.effectOnBasket
    ++ Alpha.encode message.tradeReportText
    ++ Alpha.encode message.pad6

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
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
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
    ++ encodeUIntLE 4 message.individualAllocId
    ++ encodeUIntLE 2 message.partySubIdType
    ++ encodeUInt 1 message.side
    ++ encodeUInt 1 message.instrmtMatchSideId
    ++ encodeUInt 1 message.tradeAllocStatus
    ++ Alpha.encode message.partyExecutingFirm
    ++ Alpha.encode message.partyExecutingTrader
    ++ Alpha.encode message.pad4

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
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end BasketSideAllocGrpComp

/-- Basket Broadcast -/
structure BasketBroadcast where
  pad2 : Alpha 2
  rbcHeaderComp : RbcHeaderComp
  basketTrdMatchId : BitVec 64
  transactTime : BitVec 64
  basketExecId : BitVec 32
  marketSegmentId : BitVec 32
  maturityMonthYear : BitVec 32
  basketProfileId : BitVec 32
  trdType : BitVec 16
  tradeReportType : BitVec 8
  basketTradeReportType : BitVec 8
  messageEventSource : MessageEventSource
  basketAnonymity : BitVec 8
  optionalEarlyTerminationIndicator : BitVec 8
  basketTradeReportText : Alpha 20
  tradeReportId : Alpha 20
  pad5 : Alpha 5
  basketRootPartyGrpComp : Bounded 1 BasketRootPartyGrpComp
  instrmtMatchSideGrpComp : Bounded 1 InstrmtMatchSideGrpComp
  basketSideAllocGrpComp : Bounded 2 BasketSideAllocGrpComp
  deriving DecidableEq, Repr

namespace BasketBroadcast

def encode (message : BasketBroadcast) : List UInt8 :=
  Alpha.encode message.pad2
    ++ RbcHeaderComp.encode message.rbcHeaderComp
    ++ encodeUIntLE 8 message.basketTrdMatchId
    ++ encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 4 message.basketExecId
    ++ encodeUIntLE 4 message.marketSegmentId
    ++ encodeUIntLE 4 message.maturityMonthYear
    ++ encodeUIntLE 4 message.basketProfileId
    ++ encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.basketSideAllocGrpComp.val.length)
    ++ encodeUIntLE 2 message.trdType
    ++ encodeUInt 1 message.tradeReportType
    ++ encodeUInt 1 message.basketTradeReportType
    ++ MessageEventSource.encode message.messageEventSource
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.basketRootPartyGrpComp.val.length)
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.instrmtMatchSideGrpComp.val.length)
    ++ encodeUInt 1 message.basketAnonymity
    ++ encodeUInt 1 message.optionalEarlyTerminationIndicator
    ++ Alpha.encode message.basketTradeReportText
    ++ Alpha.encode message.tradeReportId
    ++ Alpha.encode message.pad5
    ++ encodeMany BasketRootPartyGrpComp.encode message.basketRootPartyGrpComp.val
    ++ encodeMany InstrmtMatchSideGrpComp.encode message.instrmtMatchSideGrpComp.val
    ++ encodeMany BasketSideAllocGrpComp.encode message.basketSideAllocGrpComp.val

def decode (bytes : List UInt8) : Option (BasketBroadcast × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderComp, bytes) ← RbcHeaderComp.decode bytes
  let (basketTrdMatchId, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (basketExecId, bytes) ← decodeUIntLE 4 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (maturityMonthYear, bytes) ← decodeUIntLE 4 bytes
  let (basketProfileId, bytes) ← decodeUIntLE 4 bytes
  let (noBasketSideAlloc, bytes) ← decodeUIntLE 2 bytes
  let (trdType, bytes) ← decodeUIntLE 2 bytes
  let (tradeReportType, bytes) ← decodeUInt 1 bytes
  let (basketTradeReportType, bytes) ← decodeUInt 1 bytes
  let (messageEventSource, bytes) ← MessageEventSource.decode bytes
  let (noBasketRootPartyGrpsBc, bytes) ← decodeUInt 1 bytes
  let (noInstrmtMatchSides, bytes) ← decodeUInt 1 bytes
  let (basketAnonymity, bytes) ← decodeUInt 1 bytes
  let (optionalEarlyTerminationIndicator, bytes) ← decodeUInt 1 bytes
  let (basketTradeReportText, bytes) ← Alpha.decode 20 bytes
  let (tradeReportId, bytes) ← Alpha.decode 20 bytes
  let (pad5, bytes) ← Alpha.decode 5 bytes
  let (basketRootPartyGrpComp_, bytes) ← decodeMany BasketRootPartyGrpComp.decode noBasketRootPartyGrpsBc.toNat bytes
  let (instrmtMatchSideGrpComp_, bytes) ← decodeMany InstrmtMatchSideGrpComp.decode noInstrmtMatchSides.toNat bytes
  let (basketSideAllocGrpComp_, bytes) ← decodeMany BasketSideAllocGrpComp.decode noBasketSideAlloc.toNat bytes
  if fits_basketRootPartyGrpComp : basketRootPartyGrpComp_.length < 256 ^ 1 then
    if fits_instrmtMatchSideGrpComp : instrmtMatchSideGrpComp_.length < 256 ^ 1 then
      if fits_basketSideAllocGrpComp : basketSideAllocGrpComp_.length < 256 ^ 2 then
        pure ({ pad2, rbcHeaderComp, basketTrdMatchId, transactTime, basketExecId, marketSegmentId, maturityMonthYear, basketProfileId, trdType, tradeReportType, basketTradeReportType, messageEventSource, basketAnonymity, optionalEarlyTerminationIndicator, basketTradeReportText, tradeReportId, pad5, basketRootPartyGrpComp := ⟨basketRootPartyGrpComp_, fits_basketRootPartyGrpComp⟩, instrmtMatchSideGrpComp := ⟨instrmtMatchSideGrpComp_, fits_instrmtMatchSideGrpComp⟩, basketSideAllocGrpComp := ⟨basketSideAllocGrpComp_, fits_basketSideAllocGrpComp⟩ }, bytes)
      else none
    else none
  else none

theorem encode_length_pos (message : BasketBroadcast) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : BasketBroadcast) : (encode message).length ≤ 2127842 := by
  have bound_basketRootPartyGrpComp := message.basketRootPartyGrpComp.length_lt
  have bound_instrmtMatchSideGrpComp := message.instrmtMatchSideGrpComp.length_lt
  have bound_basketSideAllocGrpComp := message.basketSideAllocGrpComp.length_lt
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RbcHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length, MessageEventSource.encode_length, encodeMany_length_const BasketRootPartyGrpComp.encode 40 BasketRootPartyGrpComp.encode_length, encodeMany_length_const InstrmtMatchSideGrpComp.encode 80 InstrmtMatchSideGrpComp.encode_length, encodeMany_length_const BasketSideAllocGrpComp.encode 32 BasketSideAllocGrpComp.encode_length]
  omega

@[simp] theorem decode_encode (message : BasketBroadcast) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [RbcHeaderComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [MessageEventSource.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 BasketRootPartyGrpComp.encode BasketRootPartyGrpComp.decode BasketRootPartyGrpComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 InstrmtMatchSideGrpComp.encode InstrmtMatchSideGrpComp.decode InstrmtMatchSideGrpComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 2 BasketSideAllocGrpComp.encode BasketSideAllocGrpComp.decode BasketSideAllocGrpComp.decode_encode]
  simp only [Option.bind_some]
  simp only [message.basketRootPartyGrpComp.length_lt, message.instrmtMatchSideGrpComp.length_lt, message.basketSideAllocGrpComp.length_lt, ↓reduceDIte]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : BasketBroadcast) : decode (encode message) = some (message, []) := by
  have trailing := decode_encode message []
  rw [List.append_nil] at trailing
  exact trailing

end BasketBroadcast

/-- Basket Delete Broadcast: 90 bytes -/
structure BasketDeleteBroadcast where
  pad2 : Alpha 2
  rbcHeaderComp : RbcHeaderComp
  basketTrdMatchId : BitVec 64
  transactTime : BitVec 64
  marketSegmentId : BitVec 32
  basketExecId : BitVec 32
  basketProfileId : BitVec 32
  trdType : BitVec 16
  deleteReason : BitVec 8
  messageEventSource : MessageEventSource
  tradeReportId : Alpha 20
  pad4 : Alpha 4
  deriving DecidableEq, Repr

namespace BasketDeleteBroadcast

def encode (message : BasketDeleteBroadcast) : List UInt8 :=
  Alpha.encode message.pad2
    ++ RbcHeaderComp.encode message.rbcHeaderComp
    ++ encodeUIntLE 8 message.basketTrdMatchId
    ++ encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 4 message.marketSegmentId
    ++ encodeUIntLE 4 message.basketExecId
    ++ encodeUIntLE 4 message.basketProfileId
    ++ encodeUIntLE 2 message.trdType
    ++ encodeUInt 1 message.deleteReason
    ++ MessageEventSource.encode message.messageEventSource
    ++ Alpha.encode message.tradeReportId
    ++ Alpha.encode message.pad4

def decode (bytes : List UInt8) : Option (BasketDeleteBroadcast × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderComp, bytes) ← RbcHeaderComp.decode bytes
  let (basketTrdMatchId, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (basketExecId, bytes) ← decodeUIntLE 4 bytes
  let (basketProfileId, bytes) ← decodeUIntLE 4 bytes
  let (trdType, bytes) ← decodeUIntLE 2 bytes
  let (deleteReason, bytes) ← decodeUInt 1 bytes
  let (messageEventSource, bytes) ← MessageEventSource.decode bytes
  let (tradeReportId, bytes) ← Alpha.decode 20 bytes
  let (pad4, bytes) ← Alpha.decode 4 bytes
  pure ({ pad2, rbcHeaderComp, basketTrdMatchId, transactTime, marketSegmentId, basketExecId, basketProfileId, trdType, deleteReason, messageEventSource, tradeReportId, pad4 }, bytes)

@[simp] theorem encode_length (message : BasketDeleteBroadcast) : (encode message).length = 90 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RbcHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length, MessageEventSource.encode_length]

theorem encode_length_pos (message : BasketDeleteBroadcast) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BasketDeleteBroadcast) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [RbcHeaderComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [MessageEventSource.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : BasketDeleteBroadcast) : decode (encode message) = some (message, []) := by
  have trailing := decode_encode message []
  rw [List.append_nil] at trailing
  exact trailing

end BasketDeleteBroadcast

/-- Basket Exec Grp Comp: 16 bytes -/
structure BasketExecGrpComp where
  packageId : BitVec 32
  sideMarketSegmentId : BitVec 32
  allocId : BitVec 32
  sideTrdSubTyp : BitVec 16
  pad2 : Alpha 2
  deriving DecidableEq, Repr

namespace BasketExecGrpComp

def encode (message : BasketExecGrpComp) : List UInt8 :=
  encodeUIntLE 4 message.packageId
    ++ encodeUIntLE 4 message.sideMarketSegmentId
    ++ encodeUIntLE 4 message.allocId
    ++ encodeUIntLE 2 message.sideTrdSubTyp
    ++ Alpha.encode message.pad2

def decode (bytes : List UInt8) : Option (BasketExecGrpComp × List UInt8) := do
  let (packageId, bytes) ← decodeUIntLE 4 bytes
  let (sideMarketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (allocId, bytes) ← decodeUIntLE 4 bytes
  let (sideTrdSubTyp, bytes) ← decodeUIntLE 2 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  pure ({ packageId, sideMarketSegmentId, allocId, sideTrdSubTyp, pad2 }, bytes)

@[simp] theorem encode_length (message : BasketExecGrpComp) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : BasketExecGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BasketExecGrpComp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end BasketExecGrpComp

/-- Basket Execution Broadcast -/
structure BasketExecutionBroadcast where
  pad2 : Alpha 2
  rbcHeaderComp : RbcHeaderComp
  basketTrdMatchId : BitVec 64
  origBasketTrdMatchId : BitVec 64
  transactTime : BitVec 64
  basketExecId : BitVec 32
  marketSegmentId : BitVec 32
  basketProfileId : BitVec 32
  trdType : BitVec 16
  tradeReportType : BitVec 8
  optionalEarlyTerminationIndicator : BitVec 8
  messageEventSource : MessageEventSource
  basketSideTradeReportId : Alpha 20
  pad2v2 : Alpha 2
  basketExecGrpComp : Bounded 1 BasketExecGrpComp
  deriving DecidableEq, Repr

namespace BasketExecutionBroadcast

def encode (message : BasketExecutionBroadcast) : List UInt8 :=
  Alpha.encode message.pad2
    ++ RbcHeaderComp.encode message.rbcHeaderComp
    ++ encodeUIntLE 8 message.basketTrdMatchId
    ++ encodeUIntLE 8 message.origBasketTrdMatchId
    ++ encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 4 message.basketExecId
    ++ encodeUIntLE 4 message.marketSegmentId
    ++ encodeUIntLE 4 message.basketProfileId
    ++ encodeUIntLE 2 message.trdType
    ++ encodeUInt 1 message.tradeReportType
    ++ encodeUInt 1 message.optionalEarlyTerminationIndicator
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.basketExecGrpComp.val.length)
    ++ MessageEventSource.encode message.messageEventSource
    ++ Alpha.encode message.basketSideTradeReportId
    ++ Alpha.encode message.pad2v2
    ++ encodeMany BasketExecGrpComp.encode message.basketExecGrpComp.val

def decode (bytes : List UInt8) : Option (BasketExecutionBroadcast × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderComp, bytes) ← RbcHeaderComp.decode bytes
  let (basketTrdMatchId, bytes) ← decodeUIntLE 8 bytes
  let (origBasketTrdMatchId, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (basketExecId, bytes) ← decodeUIntLE 4 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (basketProfileId, bytes) ← decodeUIntLE 4 bytes
  let (trdType, bytes) ← decodeUIntLE 2 bytes
  let (tradeReportType, bytes) ← decodeUInt 1 bytes
  let (optionalEarlyTerminationIndicator, bytes) ← decodeUInt 1 bytes
  let (noInstrmtMatchSides, bytes) ← decodeUInt 1 bytes
  let (messageEventSource, bytes) ← MessageEventSource.decode bytes
  let (basketSideTradeReportId, bytes) ← Alpha.decode 20 bytes
  let (pad2v2, bytes) ← Alpha.decode 2 bytes
  let (basketExecGrpComp_, bytes) ← decodeMany BasketExecGrpComp.decode noInstrmtMatchSides.toNat bytes
  if fits_basketExecGrpComp : basketExecGrpComp_.length < 256 ^ 1 then
    pure ({ pad2, rbcHeaderComp, basketTrdMatchId, origBasketTrdMatchId, transactTime, basketExecId, marketSegmentId, basketProfileId, trdType, tradeReportType, optionalEarlyTerminationIndicator, messageEventSource, basketSideTradeReportId, pad2v2, basketExecGrpComp := ⟨basketExecGrpComp_, fits_basketExecGrpComp⟩ }, bytes)
  else none

theorem encode_length_pos (message : BasketExecutionBroadcast) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : BasketExecutionBroadcast) : (encode message).length ≤ 4178 := by
  have bound_basketExecGrpComp := message.basketExecGrpComp.length_lt
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RbcHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length, MessageEventSource.encode_length, encodeMany_length_const BasketExecGrpComp.encode 16 BasketExecGrpComp.encode_length]
  omega

@[simp] theorem decode_encode (message : BasketExecutionBroadcast) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [RbcHeaderComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [MessageEventSource.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 BasketExecGrpComp.encode BasketExecGrpComp.decode BasketExecGrpComp.decode_encode]
  simp only [Option.bind_some]
  simp only [message.basketExecGrpComp.length_lt, ↓reduceDIte]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : BasketExecutionBroadcast) : decode (encode message) = some (message, []) := by
  have trailing := decode_encode message []
  rw [List.append_nil] at trailing
  exact trailing

end BasketExecutionBroadcast

/-- Response Header Comp: 24 bytes -/
structure ResponseHeaderComp where
  requestTime : BitVec 64
  sendingTime : BitVec 64
  msgSeqNum : BitVec 32
  pad4 : Alpha 4
  deriving DecidableEq, Repr

namespace ResponseHeaderComp

def encode (message : ResponseHeaderComp) : List UInt8 :=
  encodeUIntLE 8 message.requestTime
    ++ encodeUIntLE 8 message.sendingTime
    ++ encodeUIntLE 4 message.msgSeqNum
    ++ Alpha.encode message.pad4

def decode (bytes : List UInt8) : Option (ResponseHeaderComp × List UInt8) := do
  let (requestTime, bytes) ← decodeUIntLE 8 bytes
  let (sendingTime, bytes) ← decodeUIntLE 8 bytes
  let (msgSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (pad4, bytes) ← Alpha.decode 4 bytes
  pure ({ requestTime, sendingTime, msgSeqNum, pad4 }, bytes)

@[simp] theorem encode_length (message : ResponseHeaderComp) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : ResponseHeaderComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ResponseHeaderComp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end ResponseHeaderComp

/-- Basket Response: 50 bytes -/
structure BasketResponse where
  pad2 : Alpha 2
  responseHeaderComp : ResponseHeaderComp
  basketExecId : BitVec 32
  tradeReportId : Alpha 20
  deriving DecidableEq, Repr

namespace BasketResponse

def encode (message : BasketResponse) : List UInt8 :=
  Alpha.encode message.pad2
    ++ ResponseHeaderComp.encode message.responseHeaderComp
    ++ encodeUIntLE 4 message.basketExecId
    ++ Alpha.encode message.tradeReportId

def decode (bytes : List UInt8) : Option (BasketResponse × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (responseHeaderComp, bytes) ← ResponseHeaderComp.decode bytes
  let (basketExecId, bytes) ← decodeUIntLE 4 bytes
  let (tradeReportId, bytes) ← Alpha.decode 20 bytes
  pure ({ pad2, responseHeaderComp, basketExecId, tradeReportId }, bytes)

@[simp] theorem encode_length (message : BasketResponse) : (encode message).length = 50 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, ResponseHeaderComp.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : BasketResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BasketResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [ResponseHeaderComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : BasketResponse) : decode (encode message) = some (message, []) := by
  have trailing := decode_encode message []
  rw [List.append_nil] at trailing
  exact trailing

end BasketResponse

/-- Old Basket Data Bc Grp Comp: 72 bytes -/
structure OldBasketDataBcGrpComp where
  transactTime : BitVec 64
  basketTrdMatchId : BitVec 64
  origBasketTrdMatchId : BitVec 64
  maturityMonthYear : BitVec 32
  optionalEarlyTerminationIndicator : BitVec 8
  basketTradeReportType : BitVec 8
  tradeReportId : Alpha 20
  basketTradeReportText : Alpha 20
  pad2 : Alpha 2
  deriving DecidableEq, Repr

namespace OldBasketDataBcGrpComp

def encode (message : OldBasketDataBcGrpComp) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 8 message.basketTrdMatchId
    ++ encodeUIntLE 8 message.origBasketTrdMatchId
    ++ encodeUIntLE 4 message.maturityMonthYear
    ++ encodeUInt 1 message.optionalEarlyTerminationIndicator
    ++ encodeUInt 1 message.basketTradeReportType
    ++ Alpha.encode message.tradeReportId
    ++ Alpha.encode message.basketTradeReportText
    ++ Alpha.encode message.pad2

def decode (bytes : List UInt8) : Option (OldBasketDataBcGrpComp × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (basketTrdMatchId, bytes) ← decodeUIntLE 8 bytes
  let (origBasketTrdMatchId, bytes) ← decodeUIntLE 8 bytes
  let (maturityMonthYear, bytes) ← decodeUIntLE 4 bytes
  let (optionalEarlyTerminationIndicator, bytes) ← decodeUInt 1 bytes
  let (basketTradeReportType, bytes) ← decodeUInt 1 bytes
  let (tradeReportId, bytes) ← Alpha.decode 20 bytes
  let (basketTradeReportText, bytes) ← Alpha.decode 20 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  pure ({ transactTime, basketTrdMatchId, origBasketTrdMatchId, maturityMonthYear, optionalEarlyTerminationIndicator, basketTradeReportType, tradeReportId, basketTradeReportText, pad2 }, bytes)

@[simp] theorem encode_length (message : OldBasketDataBcGrpComp) : (encode message).length = 72 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : OldBasketDataBcGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OldBasketDataBcGrpComp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end OldBasketDataBcGrpComp

/-- New Basket Data Bc Grp Comp: 72 bytes -/
structure NewBasketDataBcGrpComp where
  transactTime : BitVec 64
  basketTrdMatchId : BitVec 64
  origBasketTrdMatchId : BitVec 64
  maturityMonthYear : BitVec 32
  optionalEarlyTerminationIndicator : BitVec 8
  basketTradeReportType : BitVec 8
  tradeReportId : Alpha 20
  basketTradeReportText : Alpha 20
  pad2 : Alpha 2
  deriving DecidableEq, Repr

namespace NewBasketDataBcGrpComp

def encode (message : NewBasketDataBcGrpComp) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 8 message.basketTrdMatchId
    ++ encodeUIntLE 8 message.origBasketTrdMatchId
    ++ encodeUIntLE 4 message.maturityMonthYear
    ++ encodeUInt 1 message.optionalEarlyTerminationIndicator
    ++ encodeUInt 1 message.basketTradeReportType
    ++ Alpha.encode message.tradeReportId
    ++ Alpha.encode message.basketTradeReportText
    ++ Alpha.encode message.pad2

def decode (bytes : List UInt8) : Option (NewBasketDataBcGrpComp × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (basketTrdMatchId, bytes) ← decodeUIntLE 8 bytes
  let (origBasketTrdMatchId, bytes) ← decodeUIntLE 8 bytes
  let (maturityMonthYear, bytes) ← decodeUIntLE 4 bytes
  let (optionalEarlyTerminationIndicator, bytes) ← decodeUInt 1 bytes
  let (basketTradeReportType, bytes) ← decodeUInt 1 bytes
  let (tradeReportId, bytes) ← Alpha.decode 20 bytes
  let (basketTradeReportText, bytes) ← Alpha.decode 20 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  pure ({ transactTime, basketTrdMatchId, origBasketTrdMatchId, maturityMonthYear, optionalEarlyTerminationIndicator, basketTradeReportType, tradeReportId, basketTradeReportText, pad2 }, bytes)

@[simp] theorem encode_length (message : NewBasketDataBcGrpComp) : (encode message).length = 72 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : NewBasketDataBcGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NewBasketDataBcGrpComp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end NewBasketDataBcGrpComp

/-- Old Basket Instrmt Match Side Grp Comp: 80 bytes -/
structure OldBasketInstrmtMatchSideGrpComp where
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

namespace OldBasketInstrmtMatchSideGrpComp

def encode (message : OldBasketInstrmtMatchSideGrpComp) : List UInt8 :=
  encodeUIntLE 8 message.securityId
    ++ encodeUIntLE 8 message.lastPx
    ++ encodeUIntLE 8 message.transBkdTime
    ++ encodeUIntLE 8 message.relatedClosePrice
    ++ encodeUIntLE 8 message.clearingTradePrice
    ++ encodeUIntLE 4 message.packageId
    ++ encodeUIntLE 4 message.sideMarketSegmentId
    ++ encodeUIntLE 2 message.sideTrdSubTyp
    ++ encodeUInt 1 message.productComplex
    ++ encodeUInt 1 message.tradePublishIndicator
    ++ encodeUInt 1 message.instrmtMatchSideId
    ++ encodeUInt 1 message.effectOnBasket
    ++ Alpha.encode message.tradeReportText
    ++ Alpha.encode message.pad6

def decode (bytes : List UInt8) : Option (OldBasketInstrmtMatchSideGrpComp × List UInt8) := do
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

@[simp] theorem encode_length (message : OldBasketInstrmtMatchSideGrpComp) : (encode message).length = 80 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : OldBasketInstrmtMatchSideGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OldBasketInstrmtMatchSideGrpComp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end OldBasketInstrmtMatchSideGrpComp

/-- New Basket Instrmt Match Side Grp Comp: 80 bytes -/
structure NewBasketInstrmtMatchSideGrpComp where
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

namespace NewBasketInstrmtMatchSideGrpComp

def encode (message : NewBasketInstrmtMatchSideGrpComp) : List UInt8 :=
  encodeUIntLE 8 message.securityId
    ++ encodeUIntLE 8 message.lastPx
    ++ encodeUIntLE 8 message.transBkdTime
    ++ encodeUIntLE 8 message.relatedClosePrice
    ++ encodeUIntLE 8 message.clearingTradePrice
    ++ encodeUIntLE 4 message.packageId
    ++ encodeUIntLE 4 message.sideMarketSegmentId
    ++ encodeUIntLE 2 message.sideTrdSubTyp
    ++ encodeUInt 1 message.productComplex
    ++ encodeUInt 1 message.tradePublishIndicator
    ++ encodeUInt 1 message.instrmtMatchSideId
    ++ encodeUInt 1 message.effectOnBasket
    ++ Alpha.encode message.tradeReportText
    ++ Alpha.encode message.pad6

def decode (bytes : List UInt8) : Option (NewBasketInstrmtMatchSideGrpComp × List UInt8) := do
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

@[simp] theorem encode_length (message : NewBasketInstrmtMatchSideGrpComp) : (encode message).length = 80 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : NewBasketInstrmtMatchSideGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NewBasketInstrmtMatchSideGrpComp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end NewBasketInstrmtMatchSideGrpComp

/-- Old Basket Side Alloc Grp Comp: 32 bytes -/
structure OldBasketSideAllocGrpComp where
  allocQty : BitVec 64
  individualAllocId : BitVec 32
  partySubIdType : BitVec 16
  side : BitVec 8
  positionEffect : PositionEffect
  instrmtMatchSideId : BitVec 8
  tradeAllocStatus : BitVec 8
  partyExecutingFirm : Alpha 5
  partyExecutingTrader : Alpha 6
  pad3 : Alpha 3
  deriving DecidableEq, Repr

namespace OldBasketSideAllocGrpComp

def encode (message : OldBasketSideAllocGrpComp) : List UInt8 :=
  encodeUIntLE 8 message.allocQty
    ++ encodeUIntLE 4 message.individualAllocId
    ++ encodeUIntLE 2 message.partySubIdType
    ++ encodeUInt 1 message.side
    ++ PositionEffect.encode message.positionEffect
    ++ encodeUInt 1 message.instrmtMatchSideId
    ++ encodeUInt 1 message.tradeAllocStatus
    ++ Alpha.encode message.partyExecutingFirm
    ++ Alpha.encode message.partyExecutingTrader
    ++ Alpha.encode message.pad3

def decode (bytes : List UInt8) : Option (OldBasketSideAllocGrpComp × List UInt8) := do
  let (allocQty, bytes) ← decodeUIntLE 8 bytes
  let (individualAllocId, bytes) ← decodeUIntLE 4 bytes
  let (partySubIdType, bytes) ← decodeUIntLE 2 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (positionEffect, bytes) ← PositionEffect.decode bytes
  let (instrmtMatchSideId, bytes) ← decodeUInt 1 bytes
  let (tradeAllocStatus, bytes) ← decodeUInt 1 bytes
  let (partyExecutingFirm, bytes) ← Alpha.decode 5 bytes
  let (partyExecutingTrader, bytes) ← Alpha.decode 6 bytes
  let (pad3, bytes) ← Alpha.decode 3 bytes
  pure ({ allocQty, individualAllocId, partySubIdType, side, positionEffect, instrmtMatchSideId, tradeAllocStatus, partyExecutingFirm, partyExecutingTrader, pad3 }, bytes)

@[simp] theorem encode_length (message : OldBasketSideAllocGrpComp) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, PositionEffect.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : OldBasketSideAllocGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OldBasketSideAllocGrpComp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [PositionEffect.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end OldBasketSideAllocGrpComp

/-- New Basket Side Alloc Grp Comp: 32 bytes -/
structure NewBasketSideAllocGrpComp where
  allocQty : BitVec 64
  individualAllocId : BitVec 32
  partySubIdType : BitVec 16
  side : BitVec 8
  positionEffect : PositionEffect
  instrmtMatchSideId : BitVec 8
  tradeAllocStatus : BitVec 8
  partyExecutingFirm : Alpha 5
  partyExecutingTrader : Alpha 6
  pad3 : Alpha 3
  deriving DecidableEq, Repr

namespace NewBasketSideAllocGrpComp

def encode (message : NewBasketSideAllocGrpComp) : List UInt8 :=
  encodeUIntLE 8 message.allocQty
    ++ encodeUIntLE 4 message.individualAllocId
    ++ encodeUIntLE 2 message.partySubIdType
    ++ encodeUInt 1 message.side
    ++ PositionEffect.encode message.positionEffect
    ++ encodeUInt 1 message.instrmtMatchSideId
    ++ encodeUInt 1 message.tradeAllocStatus
    ++ Alpha.encode message.partyExecutingFirm
    ++ Alpha.encode message.partyExecutingTrader
    ++ Alpha.encode message.pad3

def decode (bytes : List UInt8) : Option (NewBasketSideAllocGrpComp × List UInt8) := do
  let (allocQty, bytes) ← decodeUIntLE 8 bytes
  let (individualAllocId, bytes) ← decodeUIntLE 4 bytes
  let (partySubIdType, bytes) ← decodeUIntLE 2 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (positionEffect, bytes) ← PositionEffect.decode bytes
  let (instrmtMatchSideId, bytes) ← decodeUInt 1 bytes
  let (tradeAllocStatus, bytes) ← decodeUInt 1 bytes
  let (partyExecutingFirm, bytes) ← Alpha.decode 5 bytes
  let (partyExecutingTrader, bytes) ← Alpha.decode 6 bytes
  let (pad3, bytes) ← Alpha.decode 3 bytes
  pure ({ allocQty, individualAllocId, partySubIdType, side, positionEffect, instrmtMatchSideId, tradeAllocStatus, partyExecutingFirm, partyExecutingTrader, pad3 }, bytes)

@[simp] theorem encode_length (message : NewBasketSideAllocGrpComp) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, PositionEffect.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : NewBasketSideAllocGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NewBasketSideAllocGrpComp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [PositionEffect.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end NewBasketSideAllocGrpComp

/-- Basket Roll Broadcast -/
structure BasketRollBroadcast where
  pad2 : Alpha 2
  rbcHeaderComp : RbcHeaderComp
  basketExecId : BitVec 32
  marketSegmentId : BitVec 32
  basketProfileId : BitVec 32
  trdType : BitVec 16
  tradeReportType : BitVec 8
  messageEventSource : MessageEventSource
  basketAnonymity : BitVec 8
  basketTradeReportText : Alpha 20
  tradeReportId : Alpha 20
  oldBasketDataBcGrpComp : OldBasketDataBcGrpComp
  newBasketDataBcGrpComp : NewBasketDataBcGrpComp
  basketRootPartyGrpComp : Bounded 1 BasketRootPartyGrpComp
  oldBasketInstrmtMatchSideGrpComp : Bounded 1 OldBasketInstrmtMatchSideGrpComp
  newBasketInstrmtMatchSideGrpComp : Bounded 1 NewBasketInstrmtMatchSideGrpComp
  oldBasketSideAllocGrpComp : Bounded 2 OldBasketSideAllocGrpComp
  newBasketSideAllocGrpComp : Bounded 2 NewBasketSideAllocGrpComp
  deriving DecidableEq, Repr

namespace BasketRollBroadcast

def encode (message : BasketRollBroadcast) : List UInt8 :=
  Alpha.encode message.pad2
    ++ RbcHeaderComp.encode message.rbcHeaderComp
    ++ encodeUIntLE 4 message.basketExecId
    ++ encodeUIntLE 4 message.marketSegmentId
    ++ encodeUIntLE 4 message.basketProfileId
    ++ encodeUIntLE 2 message.trdType
    ++ encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.oldBasketSideAllocGrpComp.val.length)
    ++ encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.newBasketSideAllocGrpComp.val.length)
    ++ encodeUInt 1 message.tradeReportType
    ++ MessageEventSource.encode message.messageEventSource
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.basketRootPartyGrpComp.val.length)
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.oldBasketInstrmtMatchSideGrpComp.val.length)
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.newBasketInstrmtMatchSideGrpComp.val.length)
    ++ encodeUInt 1 message.basketAnonymity
    ++ Alpha.encode message.basketTradeReportText
    ++ Alpha.encode message.tradeReportId
    ++ OldBasketDataBcGrpComp.encode message.oldBasketDataBcGrpComp
    ++ NewBasketDataBcGrpComp.encode message.newBasketDataBcGrpComp
    ++ encodeMany BasketRootPartyGrpComp.encode message.basketRootPartyGrpComp.val
    ++ encodeMany OldBasketInstrmtMatchSideGrpComp.encode message.oldBasketInstrmtMatchSideGrpComp.val
    ++ encodeMany NewBasketInstrmtMatchSideGrpComp.encode message.newBasketInstrmtMatchSideGrpComp.val
    ++ encodeMany OldBasketSideAllocGrpComp.encode message.oldBasketSideAllocGrpComp.val
    ++ encodeMany NewBasketSideAllocGrpComp.encode message.newBasketSideAllocGrpComp.val

def decode (bytes : List UInt8) : Option (BasketRollBroadcast × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderComp, bytes) ← RbcHeaderComp.decode bytes
  let (basketExecId, bytes) ← decodeUIntLE 4 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (basketProfileId, bytes) ← decodeUIntLE 4 bytes
  let (trdType, bytes) ← decodeUIntLE 2 bytes
  let (noOldBasketSideAlloc, bytes) ← decodeUIntLE 2 bytes
  let (noNewBasketSideAlloc, bytes) ← decodeUIntLE 2 bytes
  let (tradeReportType, bytes) ← decodeUInt 1 bytes
  let (messageEventSource, bytes) ← MessageEventSource.decode bytes
  let (noBasketRootPartyGrpsBc, bytes) ← decodeUInt 1 bytes
  let (noOldBasketInstrmtMatchSides, bytes) ← decodeUInt 1 bytes
  let (noNewBasketInstrmtMatchSides, bytes) ← decodeUInt 1 bytes
  let (basketAnonymity, bytes) ← decodeUInt 1 bytes
  let (basketTradeReportText, bytes) ← Alpha.decode 20 bytes
  let (tradeReportId, bytes) ← Alpha.decode 20 bytes
  let (oldBasketDataBcGrpComp, bytes) ← OldBasketDataBcGrpComp.decode bytes
  let (newBasketDataBcGrpComp, bytes) ← NewBasketDataBcGrpComp.decode bytes
  let (basketRootPartyGrpComp_, bytes) ← decodeMany BasketRootPartyGrpComp.decode noBasketRootPartyGrpsBc.toNat bytes
  let (oldBasketInstrmtMatchSideGrpComp_, bytes) ← decodeMany OldBasketInstrmtMatchSideGrpComp.decode noOldBasketInstrmtMatchSides.toNat bytes
  let (newBasketInstrmtMatchSideGrpComp_, bytes) ← decodeMany NewBasketInstrmtMatchSideGrpComp.decode noNewBasketInstrmtMatchSides.toNat bytes
  let (oldBasketSideAllocGrpComp_, bytes) ← decodeMany OldBasketSideAllocGrpComp.decode noOldBasketSideAlloc.toNat bytes
  let (newBasketSideAllocGrpComp_, bytes) ← decodeMany NewBasketSideAllocGrpComp.decode noNewBasketSideAlloc.toNat bytes
  if fits_basketRootPartyGrpComp : basketRootPartyGrpComp_.length < 256 ^ 1 then
    if fits_oldBasketInstrmtMatchSideGrpComp : oldBasketInstrmtMatchSideGrpComp_.length < 256 ^ 1 then
      if fits_newBasketInstrmtMatchSideGrpComp : newBasketInstrmtMatchSideGrpComp_.length < 256 ^ 1 then
        if fits_oldBasketSideAllocGrpComp : oldBasketSideAllocGrpComp_.length < 256 ^ 2 then
          if fits_newBasketSideAllocGrpComp : newBasketSideAllocGrpComp_.length < 256 ^ 2 then
            pure ({ pad2, rbcHeaderComp, basketExecId, marketSegmentId, basketProfileId, trdType, tradeReportType, messageEventSource, basketAnonymity, basketTradeReportText, tradeReportId, oldBasketDataBcGrpComp, newBasketDataBcGrpComp, basketRootPartyGrpComp := ⟨basketRootPartyGrpComp_, fits_basketRootPartyGrpComp⟩, oldBasketInstrmtMatchSideGrpComp := ⟨oldBasketInstrmtMatchSideGrpComp_, fits_oldBasketInstrmtMatchSideGrpComp⟩, newBasketInstrmtMatchSideGrpComp := ⟨newBasketInstrmtMatchSideGrpComp_, fits_newBasketInstrmtMatchSideGrpComp⟩, oldBasketSideAllocGrpComp := ⟨oldBasketSideAllocGrpComp_, fits_oldBasketSideAllocGrpComp⟩, newBasketSideAllocGrpComp := ⟨newBasketSideAllocGrpComp_, fits_newBasketSideAllocGrpComp⟩ }, bytes)
          else none
        else none
      else none
    else none
  else none

theorem encode_length_pos (message : BasketRollBroadcast) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : BasketRollBroadcast) : (encode message).length ≤ 4245482 := by
  have bound_basketRootPartyGrpComp := message.basketRootPartyGrpComp.length_lt
  have bound_oldBasketInstrmtMatchSideGrpComp := message.oldBasketInstrmtMatchSideGrpComp.length_lt
  have bound_newBasketInstrmtMatchSideGrpComp := message.newBasketInstrmtMatchSideGrpComp.length_lt
  have bound_oldBasketSideAllocGrpComp := message.oldBasketSideAllocGrpComp.length_lt
  have bound_newBasketSideAllocGrpComp := message.newBasketSideAllocGrpComp.length_lt
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RbcHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length, MessageEventSource.encode_length, OldBasketDataBcGrpComp.encode_length, NewBasketDataBcGrpComp.encode_length, encodeMany_length_const BasketRootPartyGrpComp.encode 40 BasketRootPartyGrpComp.encode_length, encodeMany_length_const OldBasketInstrmtMatchSideGrpComp.encode 80 OldBasketInstrmtMatchSideGrpComp.encode_length, encodeMany_length_const NewBasketInstrmtMatchSideGrpComp.encode 80 NewBasketInstrmtMatchSideGrpComp.encode_length, encodeMany_length_const OldBasketSideAllocGrpComp.encode 32 OldBasketSideAllocGrpComp.encode_length, encodeMany_length_const NewBasketSideAllocGrpComp.encode 32 NewBasketSideAllocGrpComp.encode_length]
  omega

@[simp] theorem decode_encode (message : BasketRollBroadcast) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [RbcHeaderComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [MessageEventSource.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [OldBasketDataBcGrpComp.decode_encode]
  simp only [Option.bind_some]
  rw [NewBasketDataBcGrpComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 BasketRootPartyGrpComp.encode BasketRootPartyGrpComp.decode BasketRootPartyGrpComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 OldBasketInstrmtMatchSideGrpComp.encode OldBasketInstrmtMatchSideGrpComp.decode OldBasketInstrmtMatchSideGrpComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 NewBasketInstrmtMatchSideGrpComp.encode NewBasketInstrmtMatchSideGrpComp.decode NewBasketInstrmtMatchSideGrpComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 2 OldBasketSideAllocGrpComp.encode OldBasketSideAllocGrpComp.decode OldBasketSideAllocGrpComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 2 NewBasketSideAllocGrpComp.encode NewBasketSideAllocGrpComp.decode NewBasketSideAllocGrpComp.decode_encode]
  simp only [Option.bind_some]
  simp only [message.basketRootPartyGrpComp.length_lt, message.oldBasketInstrmtMatchSideGrpComp.length_lt, message.newBasketInstrmtMatchSideGrpComp.length_lt, message.oldBasketSideAllocGrpComp.length_lt, message.newBasketSideAllocGrpComp.length_lt, ↓reduceDIte]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : BasketRollBroadcast) : decode (encode message) = some (message, []) := by
  have trailing := decode_encode message []
  rw [List.append_nil] at trailing
  exact trailing

end BasketRollBroadcast

/-- Notif Header Comp: 8 bytes -/
structure NotifHeaderComp where
  sendingTime : BitVec 64
  deriving DecidableEq, Repr

namespace NotifHeaderComp

def encode (message : NotifHeaderComp) : List UInt8 :=
  encodeUIntLE 8 message.sendingTime

def decode (bytes : List UInt8) : Option (NotifHeaderComp × List UInt8) := do
  let (sendingTime, bytes) ← decodeUIntLE 8 bytes
  pure ({ sendingTime }, bytes)

@[simp] theorem encode_length (message : NotifHeaderComp) : (encode message).length = 8 := by
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : NotifHeaderComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NotifHeaderComp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

end NotifHeaderComp

/-- Broadcast Error Notification -/
structure BroadcastErrorNotification where
  pad2 : Alpha 2
  notifHeaderComp : NotifHeaderComp
  applIdStatus : BitVec 32
  refApplSubId : BitVec 32
  refApplId : BitVec 8
  sessionStatus : BitVec 8
  varText : Bounded 2 UInt8
  alignmentPadding : Capped 4282374239
  deriving DecidableEq, Repr

namespace BroadcastErrorNotification

def encode (message : BroadcastErrorNotification) : List UInt8 :=
  Alpha.encode message.pad2
    ++ NotifHeaderComp.encode message.notifHeaderComp
    ++ encodeUIntLE 4 message.applIdStatus
    ++ encodeUIntLE 4 message.refApplSubId
    ++ encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.varText.val.length)
    ++ encodeUInt 1 message.refApplId
    ++ encodeUInt 1 message.sessionStatus
    ++ encodeMany Byte.encode message.varText.val
    ++ message.alignmentPadding.val

def decode (bytes : List UInt8) : Option BroadcastErrorNotification := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (notifHeaderComp, bytes) ← NotifHeaderComp.decode bytes
  let (applIdStatus, bytes) ← decodeUIntLE 4 bytes
  let (refApplSubId, bytes) ← decodeUIntLE 4 bytes
  let (varTextLen, bytes) ← decodeUIntLE 2 bytes
  let (refApplId, bytes) ← decodeUInt 1 bytes
  let (sessionStatus, bytes) ← decodeUInt 1 bytes
  let (varText_, bytes) ← decodeMany Byte.decode varTextLen.toNat bytes
  let alignmentPadding_ := bytes
  if fits_varText : varText_.length < 256 ^ 2 then
    if fits_alignmentPadding : alignmentPadding_.length ≤ 4282374239 then
      pure { pad2, notifHeaderComp, applIdStatus, refApplSubId, refApplId, sessionStatus, varText := ⟨varText_, fits_varText⟩, alignmentPadding := ⟨alignmentPadding_, fits_alignmentPadding⟩ }
    else none
  else none

theorem encode_length_pos (message : BroadcastErrorNotification) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : BroadcastErrorNotification) : (encode message).length ≤ 4282439796 := by
  have bound_varText := message.varText.length_lt
  have bound_alignmentPadding := message.alignmentPadding.length_le
  unfold encode
  simp only [List.length_append, Alpha.encode_length, NotifHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const Byte.encode 1 Byte.encode_length]
  omega

theorem decode_encode (message : BroadcastErrorNotification) : decode (encode message) = some message := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [NotifHeaderComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 2 Byte.encode Byte.decode Byte.decode_encode]
  simp only [Option.bind_some]
  simp only [message.varText.length_lt, message.alignmentPadding.length_le, ↓reduceDIte]
  rfl

end BroadcastErrorNotification

/-- Rbc Header Me Comp: 56 bytes -/
structure RbcHeaderMeComp where
  trdRegTsTimeOut : BitVec 64
  notificationIn : BitVec 64
  sendingTime : BitVec 64
  applSubId : BitVec 32
  partitionId : BitVec 16
  applMsgId : Alpha 16
  applId : BitVec 8
  applResendFlag : BitVec 8
  lastFragment : BitVec 8
  pad7 : Alpha 7
  deriving DecidableEq, Repr

namespace RbcHeaderMeComp

def encode (message : RbcHeaderMeComp) : List UInt8 :=
  encodeUIntLE 8 message.trdRegTsTimeOut
    ++ encodeUIntLE 8 message.notificationIn
    ++ encodeUIntLE 8 message.sendingTime
    ++ encodeUIntLE 4 message.applSubId
    ++ encodeUIntLE 2 message.partitionId
    ++ Alpha.encode message.applMsgId
    ++ encodeUInt 1 message.applId
    ++ encodeUInt 1 message.applResendFlag
    ++ encodeUInt 1 message.lastFragment
    ++ Alpha.encode message.pad7

def decode (bytes : List UInt8) : Option (RbcHeaderMeComp × List UInt8) := do
  let (trdRegTsTimeOut, bytes) ← decodeUIntLE 8 bytes
  let (notificationIn, bytes) ← decodeUIntLE 8 bytes
  let (sendingTime, bytes) ← decodeUIntLE 8 bytes
  let (applSubId, bytes) ← decodeUIntLE 4 bytes
  let (partitionId, bytes) ← decodeUIntLE 2 bytes
  let (applMsgId, bytes) ← Alpha.decode 16 bytes
  let (applId, bytes) ← decodeUInt 1 bytes
  let (applResendFlag, bytes) ← decodeUInt 1 bytes
  let (lastFragment, bytes) ← decodeUInt 1 bytes
  let (pad7, bytes) ← Alpha.decode 7 bytes
  pure ({ trdRegTsTimeOut, notificationIn, sendingTime, applSubId, partitionId, applMsgId, applId, applResendFlag, lastFragment, pad7 }, bytes)

@[simp] theorem encode_length (message : RbcHeaderMeComp) : (encode message).length = 56 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : RbcHeaderMeComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RbcHeaderMeComp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end RbcHeaderMeComp

/-- Clip Deletion Notification: 122 bytes -/
structure ClipDeletionNotification where
  pad2 : Alpha 2
  rbcHeaderMeComp : RbcHeaderMeComp
  clOrdId : BitVec 64
  origClOrdId : BitVec 64
  orderId : BitVec 64
  execId : BitVec 64
  securityId : BitVec 64
  cxlQty : BitVec 64
  marketSegmentId : BitVec 32
  execRestatementReason : BitVec 16
  productComplex : BitVec 8
  side : BitVec 8
  ordStatus : OrdStatus
  execType : ExecType
  pad6 : Alpha 6
  deriving DecidableEq, Repr

namespace ClipDeletionNotification

def encode (message : ClipDeletionNotification) : List UInt8 :=
  Alpha.encode message.pad2
    ++ RbcHeaderMeComp.encode message.rbcHeaderMeComp
    ++ encodeUIntLE 8 message.clOrdId
    ++ encodeUIntLE 8 message.origClOrdId
    ++ encodeUIntLE 8 message.orderId
    ++ encodeUIntLE 8 message.execId
    ++ encodeUIntLE 8 message.securityId
    ++ encodeUIntLE 8 message.cxlQty
    ++ encodeUIntLE 4 message.marketSegmentId
    ++ encodeUIntLE 2 message.execRestatementReason
    ++ encodeUInt 1 message.productComplex
    ++ encodeUInt 1 message.side
    ++ OrdStatus.encode message.ordStatus
    ++ ExecType.encode message.execType
    ++ Alpha.encode message.pad6

def decode (bytes : List UInt8) : Option (ClipDeletionNotification × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderMeComp, bytes) ← RbcHeaderMeComp.decode bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (origClOrdId, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (cxlQty, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (execRestatementReason, bytes) ← decodeUIntLE 2 bytes
  let (productComplex, bytes) ← decodeUInt 1 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (pad6, bytes) ← Alpha.decode 6 bytes
  pure ({ pad2, rbcHeaderMeComp, clOrdId, origClOrdId, orderId, execId, securityId, cxlQty, marketSegmentId, execRestatementReason, productComplex, side, ordStatus, execType, pad6 }, bytes)

@[simp] theorem encode_length (message : ClipDeletionNotification) : (encode message).length = 122 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RbcHeaderMeComp.encode_length, encodeUIntLE_length, encodeUInt_length, OrdStatus.encode_length, ExecType.encode_length]

theorem encode_length_pos (message : ClipDeletionNotification) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ClipDeletionNotification) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [RbcHeaderMeComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [OrdStatus.decode_encode]
  simp only [Option.bind_some]
  rw [ExecType.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : ClipDeletionNotification) : decode (encode message) = some (message, []) := by
  have trailing := decode_encode message []
  rw [List.append_nil] at trailing
  exact trailing

end ClipDeletionNotification

/-- Fills Grp Comp: 32 bytes -/
structure FillsGrpComp where
  fillPx : BitVec 64
  fillQty : BitVec 64
  fillMatchId : BitVec 32
  fillExecId : BitVec 32
  fillLiquidityInd : BitVec 8
  pad7 : Alpha 7
  deriving DecidableEq, Repr

namespace FillsGrpComp

def encode (message : FillsGrpComp) : List UInt8 :=
  encodeUIntLE 8 message.fillPx
    ++ encodeUIntLE 8 message.fillQty
    ++ encodeUIntLE 4 message.fillMatchId
    ++ encodeUIntLE 4 message.fillExecId
    ++ encodeUInt 1 message.fillLiquidityInd
    ++ Alpha.encode message.pad7

def decode (bytes : List UInt8) : Option (FillsGrpComp × List UInt8) := do
  let (fillPx, bytes) ← decodeUIntLE 8 bytes
  let (fillQty, bytes) ← decodeUIntLE 8 bytes
  let (fillMatchId, bytes) ← decodeUIntLE 4 bytes
  let (fillExecId, bytes) ← decodeUIntLE 4 bytes
  let (fillLiquidityInd, bytes) ← decodeUInt 1 bytes
  let (pad7, bytes) ← Alpha.decode 7 bytes
  pure ({ fillPx, fillQty, fillMatchId, fillExecId, fillLiquidityInd, pad7 }, bytes)

@[simp] theorem encode_length (message : FillsGrpComp) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : FillsGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : FillsGrpComp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end FillsGrpComp

/-- Instrmnt Leg Exec Grp Comp: 32 bytes -/
structure InstrmntLegExecGrpComp where
  legSecurityId : BitVec 64
  legLastPx : BitVec 64
  legLastQty : BitVec 64
  legExecId : BitVec 32
  legSide : BitVec 8
  fillRefId : BitVec 8
  pad2 : Alpha 2
  deriving DecidableEq, Repr

namespace InstrmntLegExecGrpComp

def encode (message : InstrmntLegExecGrpComp) : List UInt8 :=
  encodeUIntLE 8 message.legSecurityId
    ++ encodeUIntLE 8 message.legLastPx
    ++ encodeUIntLE 8 message.legLastQty
    ++ encodeUIntLE 4 message.legExecId
    ++ encodeUInt 1 message.legSide
    ++ encodeUInt 1 message.fillRefId
    ++ Alpha.encode message.pad2

def decode (bytes : List UInt8) : Option (InstrmntLegExecGrpComp × List UInt8) := do
  let (legSecurityId, bytes) ← decodeUIntLE 8 bytes
  let (legLastPx, bytes) ← decodeUIntLE 8 bytes
  let (legLastQty, bytes) ← decodeUIntLE 8 bytes
  let (legExecId, bytes) ← decodeUIntLE 4 bytes
  let (legSide, bytes) ← decodeUInt 1 bytes
  let (fillRefId, bytes) ← decodeUInt 1 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  pure ({ legSecurityId, legLastPx, legLastQty, legExecId, legSide, fillRefId, pad2 }, bytes)

@[simp] theorem encode_length (message : InstrmntLegExecGrpComp) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : InstrmntLegExecGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstrmntLegExecGrpComp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end InstrmntLegExecGrpComp

/-- Clip Execution Notification -/
structure ClipExecutionNotification where
  pad2 : Alpha 2
  rbcHeaderMeComp : RbcHeaderMeComp
  clOrdId : BitVec 64
  origClOrdId : BitVec 64
  orderId : BitVec 64
  execId : BitVec 64
  securityId : BitVec 64
  cxlQty : BitVec 64
  leavesQty : BitVec 64
  cumQty : BitVec 64
  marketSegmentId : BitVec 32
  execRestatementReason : BitVec 16
  productComplex : BitVec 8
  side : BitVec 8
  ordStatus : OrdStatus
  execType : ExecType
  matchType : BitVec 8
  pad2v2 : Alpha 2
  fillsGrpComp : Bounded 1 FillsGrpComp
  instrmntLegExecGrpComp : Bounded 2 InstrmntLegExecGrpComp
  deriving DecidableEq, Repr

namespace ClipExecutionNotification

def encode (message : ClipExecutionNotification) : List UInt8 :=
  Alpha.encode message.pad2
    ++ RbcHeaderMeComp.encode message.rbcHeaderMeComp
    ++ encodeUIntLE 8 message.clOrdId
    ++ encodeUIntLE 8 message.origClOrdId
    ++ encodeUIntLE 8 message.orderId
    ++ encodeUIntLE 8 message.execId
    ++ encodeUIntLE 8 message.securityId
    ++ encodeUIntLE 8 message.cxlQty
    ++ encodeUIntLE 8 message.leavesQty
    ++ encodeUIntLE 8 message.cumQty
    ++ encodeUIntLE 4 message.marketSegmentId
    ++ encodeUIntLE 2 message.execRestatementReason
    ++ encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.instrmntLegExecGrpComp.val.length)
    ++ encodeUInt 1 message.productComplex
    ++ encodeUInt 1 message.side
    ++ OrdStatus.encode message.ordStatus
    ++ ExecType.encode message.execType
    ++ encodeUInt 1 message.matchType
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.fillsGrpComp.val.length)
    ++ Alpha.encode message.pad2v2
    ++ encodeMany FillsGrpComp.encode message.fillsGrpComp.val
    ++ encodeMany InstrmntLegExecGrpComp.encode message.instrmntLegExecGrpComp.val

def decode (bytes : List UInt8) : Option (ClipExecutionNotification × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderMeComp, bytes) ← RbcHeaderMeComp.decode bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (origClOrdId, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (cxlQty, bytes) ← decodeUIntLE 8 bytes
  let (leavesQty, bytes) ← decodeUIntLE 8 bytes
  let (cumQty, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (execRestatementReason, bytes) ← decodeUIntLE 2 bytes
  let (noLegExecs, bytes) ← decodeUIntLE 2 bytes
  let (productComplex, bytes) ← decodeUInt 1 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (matchType, bytes) ← decodeUInt 1 bytes
  let (noFills, bytes) ← decodeUInt 1 bytes
  let (pad2v2, bytes) ← Alpha.decode 2 bytes
  let (fillsGrpComp_, bytes) ← decodeMany FillsGrpComp.decode noFills.toNat bytes
  let (instrmntLegExecGrpComp_, bytes) ← decodeMany InstrmntLegExecGrpComp.decode noLegExecs.toNat bytes
  if fits_fillsGrpComp : fillsGrpComp_.length < 256 ^ 1 then
    if fits_instrmntLegExecGrpComp : instrmntLegExecGrpComp_.length < 256 ^ 2 then
      pure ({ pad2, rbcHeaderMeComp, clOrdId, origClOrdId, orderId, execId, securityId, cxlQty, leavesQty, cumQty, marketSegmentId, execRestatementReason, productComplex, side, ordStatus, execType, matchType, pad2v2, fillsGrpComp := ⟨fillsGrpComp_, fits_fillsGrpComp⟩, instrmntLegExecGrpComp := ⟨instrmntLegExecGrpComp_, fits_instrmntLegExecGrpComp⟩ }, bytes)
    else none
  else none

theorem encode_length_pos (message : ClipExecutionNotification) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ClipExecutionNotification) : (encode message).length ≤ 2105418 := by
  have bound_fillsGrpComp := message.fillsGrpComp.length_lt
  have bound_instrmntLegExecGrpComp := message.instrmntLegExecGrpComp.length_lt
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RbcHeaderMeComp.encode_length, encodeUIntLE_length, encodeUInt_length, OrdStatus.encode_length, ExecType.encode_length, encodeMany_length_const FillsGrpComp.encode 32 FillsGrpComp.encode_length, encodeMany_length_const InstrmntLegExecGrpComp.encode 32 InstrmntLegExecGrpComp.encode_length]
  omega

@[simp] theorem decode_encode (message : ClipExecutionNotification) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [RbcHeaderMeComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [OrdStatus.decode_encode]
  simp only [Option.bind_some]
  rw [ExecType.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 FillsGrpComp.encode FillsGrpComp.decode FillsGrpComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 2 InstrmntLegExecGrpComp.encode InstrmntLegExecGrpComp.decode InstrmntLegExecGrpComp.decode_encode]
  simp only [Option.bind_some]
  simp only [message.fillsGrpComp.length_lt, message.instrmntLegExecGrpComp.length_lt, ↓reduceDIte]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : ClipExecutionNotification) : decode (encode message) = some (message, []) := by
  have trailing := decode_encode message []
  rw [List.append_nil] at trailing
  exact trailing

end ClipExecutionNotification

/-- Cross Request Ack Side Grp Comp: 24 bytes -/
structure CrossRequestAckSideGrpComp where
  orderId : BitVec 64
  clOrdId : BitVec 64
  inputSource : BitVec 8
  side : BitVec 8
  pad6 : Alpha 6
  deriving DecidableEq, Repr

namespace CrossRequestAckSideGrpComp

def encode (message : CrossRequestAckSideGrpComp) : List UInt8 :=
  encodeUIntLE 8 message.orderId
    ++ encodeUIntLE 8 message.clOrdId
    ++ encodeUInt 1 message.inputSource
    ++ encodeUInt 1 message.side
    ++ Alpha.encode message.pad6

def decode (bytes : List UInt8) : Option (CrossRequestAckSideGrpComp × List UInt8) := do
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (inputSource, bytes) ← decodeUInt 1 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (pad6, bytes) ← Alpha.decode 6 bytes
  pure ({ orderId, clOrdId, inputSource, side, pad6 }, bytes)

@[simp] theorem encode_length (message : CrossRequestAckSideGrpComp) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : CrossRequestAckSideGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CrossRequestAckSideGrpComp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end CrossRequestAckSideGrpComp

/-- Clip Response -/
structure ClipResponse where
  pad2 : Alpha 2
  nrResponseHeaderMeComp : NrResponseHeaderMeComp
  execId : BitVec 64
  securityId : BitVec 64
  marketSegmentId : BitVec 32
  crossRequestId : BitVec 32
  impliedCheckPriceIndicator : BitVec 8
  pad6 : Alpha 6
  crossRequestAckSideGrpComp : Bounded 1 CrossRequestAckSideGrpComp
  deriving DecidableEq, Repr

namespace ClipResponse

def encode (message : ClipResponse) : List UInt8 :=
  Alpha.encode message.pad2
    ++ NrResponseHeaderMeComp.encode message.nrResponseHeaderMeComp
    ++ encodeUIntLE 8 message.execId
    ++ encodeUIntLE 8 message.securityId
    ++ encodeUIntLE 4 message.marketSegmentId
    ++ encodeUIntLE 4 message.crossRequestId
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.crossRequestAckSideGrpComp.val.length)
    ++ encodeUInt 1 message.impliedCheckPriceIndicator
    ++ Alpha.encode message.pad6
    ++ encodeMany CrossRequestAckSideGrpComp.encode message.crossRequestAckSideGrpComp.val

def decode (bytes : List UInt8) : Option (ClipResponse × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (nrResponseHeaderMeComp, bytes) ← NrResponseHeaderMeComp.decode bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (crossRequestId, bytes) ← decodeUIntLE 4 bytes
  let (noSides, bytes) ← decodeUInt 1 bytes
  let (impliedCheckPriceIndicator, bytes) ← decodeUInt 1 bytes
  let (pad6, bytes) ← Alpha.decode 6 bytes
  let (crossRequestAckSideGrpComp_, bytes) ← decodeMany CrossRequestAckSideGrpComp.decode noSides.toNat bytes
  if fits_crossRequestAckSideGrpComp : crossRequestAckSideGrpComp_.length < 256 ^ 1 then
    pure ({ pad2, nrResponseHeaderMeComp, execId, securityId, marketSegmentId, crossRequestId, impliedCheckPriceIndicator, pad6, crossRequestAckSideGrpComp := ⟨crossRequestAckSideGrpComp_, fits_crossRequestAckSideGrpComp⟩ }, bytes)
  else none

theorem encode_length_pos (message : ClipResponse) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ClipResponse) : (encode message).length ≤ 6202 := by
  have bound_crossRequestAckSideGrpComp := message.crossRequestAckSideGrpComp.length_lt
  unfold encode
  simp only [List.length_append, Alpha.encode_length, NrResponseHeaderMeComp.encode_length, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const CrossRequestAckSideGrpComp.encode 24 CrossRequestAckSideGrpComp.encode_length]
  omega

@[simp] theorem decode_encode (message : ClipResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [NrResponseHeaderMeComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 CrossRequestAckSideGrpComp.encode CrossRequestAckSideGrpComp.decode CrossRequestAckSideGrpComp.decode_encode]
  simp only [Option.bind_some]
  simp only [message.crossRequestAckSideGrpComp.length_lt, ↓reduceDIte]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : ClipResponse) : decode (encode message) = some (message, []) := by
  have trailing := decode_encode message []
  rw [List.append_nil] at trailing
  exact trailing

end ClipResponse

/-- Cross Request Response: 58 bytes -/
structure CrossRequestResponse where
  pad2 : Alpha 2
  nrResponseHeaderMeComp : NrResponseHeaderMeComp
  execId : BitVec 64
  deriving DecidableEq, Repr

namespace CrossRequestResponse

def encode (message : CrossRequestResponse) : List UInt8 :=
  Alpha.encode message.pad2
    ++ NrResponseHeaderMeComp.encode message.nrResponseHeaderMeComp
    ++ encodeUIntLE 8 message.execId

def decode (bytes : List UInt8) : Option (CrossRequestResponse × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (nrResponseHeaderMeComp, bytes) ← NrResponseHeaderMeComp.decode bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  pure ({ pad2, nrResponseHeaderMeComp, execId }, bytes)

@[simp] theorem encode_length (message : CrossRequestResponse) : (encode message).length = 58 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, NrResponseHeaderMeComp.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : CrossRequestResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CrossRequestResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [NrResponseHeaderMeComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : CrossRequestResponse) : decode (encode message) = some (message, []) := by
  have trailing := decode_encode message []
  rw [List.append_nil] at trailing
  exact trailing

end CrossRequestResponse

/-- Not Affected Orders Grp Comp: 16 bytes -/
structure NotAffectedOrdersGrpComp where
  notAffectedOrderId : BitVec 64
  notAffOrigClOrdId : BitVec 64
  deriving DecidableEq, Repr

namespace NotAffectedOrdersGrpComp

def encode (message : NotAffectedOrdersGrpComp) : List UInt8 :=
  encodeUIntLE 8 message.notAffectedOrderId
    ++ encodeUIntLE 8 message.notAffOrigClOrdId

def decode (bytes : List UInt8) : Option (NotAffectedOrdersGrpComp × List UInt8) := do
  let (notAffectedOrderId, bytes) ← decodeUIntLE 8 bytes
  let (notAffOrigClOrdId, bytes) ← decodeUIntLE 8 bytes
  pure ({ notAffectedOrderId, notAffOrigClOrdId }, bytes)

@[simp] theorem encode_length (message : NotAffectedOrdersGrpComp) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : NotAffectedOrdersGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NotAffectedOrdersGrpComp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

end NotAffectedOrdersGrpComp

/-- Affected Order Requests Grp Comp: 8 bytes -/
structure AffectedOrderRequestsGrpComp where
  affectedOrderRequestId : BitVec 32
  pad4 : Alpha 4
  deriving DecidableEq, Repr

namespace AffectedOrderRequestsGrpComp

def encode (message : AffectedOrderRequestsGrpComp) : List UInt8 :=
  encodeUIntLE 4 message.affectedOrderRequestId
    ++ Alpha.encode message.pad4

def decode (bytes : List UInt8) : Option (AffectedOrderRequestsGrpComp × List UInt8) := do
  let (affectedOrderRequestId, bytes) ← decodeUIntLE 4 bytes
  let (pad4, bytes) ← Alpha.decode 4 bytes
  pure ({ affectedOrderRequestId, pad4 }, bytes)

@[simp] theorem encode_length (message : AffectedOrderRequestsGrpComp) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : AffectedOrderRequestsGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AffectedOrderRequestsGrpComp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end AffectedOrderRequestsGrpComp

/-- Delete All Order Broadcast -/
structure DeleteAllOrderBroadcast where
  pad2 : Alpha 2
  rbcHeaderMeComp : RbcHeaderMeComp
  massActionReportId : BitVec 64
  securityId : BitVec 64
  price : BitVec 64
  marketSegmentId : BitVec 32
  targetPartyIdSessionId : BitVec 32
  targetPartyIdExecutingTrader : BitVec 32
  partyIdEnteringTrader : BitVec 32
  partyIdEnteringFirm : BitVec 8
  massActionReason : BitVec 8
  execInst : BitVec 8
  side : BitVec 8
  notAffectedOrdersGrpComp : Bounded 2 NotAffectedOrdersGrpComp
  affectedOrderRequestsGrpComp : Bounded 2 AffectedOrderRequestsGrpComp
  deriving DecidableEq, Repr

namespace DeleteAllOrderBroadcast

def encode (message : DeleteAllOrderBroadcast) : List UInt8 :=
  Alpha.encode message.pad2
    ++ RbcHeaderMeComp.encode message.rbcHeaderMeComp
    ++ encodeUIntLE 8 message.massActionReportId
    ++ encodeUIntLE 8 message.securityId
    ++ encodeUIntLE 8 message.price
    ++ encodeUIntLE 4 message.marketSegmentId
    ++ encodeUIntLE 4 message.targetPartyIdSessionId
    ++ encodeUIntLE 4 message.targetPartyIdExecutingTrader
    ++ encodeUIntLE 4 message.partyIdEnteringTrader
    ++ encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.notAffectedOrdersGrpComp.val.length)
    ++ encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.affectedOrderRequestsGrpComp.val.length)
    ++ encodeUInt 1 message.partyIdEnteringFirm
    ++ encodeUInt 1 message.massActionReason
    ++ encodeUInt 1 message.execInst
    ++ encodeUInt 1 message.side
    ++ encodeMany NotAffectedOrdersGrpComp.encode message.notAffectedOrdersGrpComp.val
    ++ encodeMany AffectedOrderRequestsGrpComp.encode message.affectedOrderRequestsGrpComp.val

def decode (bytes : List UInt8) : Option (DeleteAllOrderBroadcast × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderMeComp, bytes) ← RbcHeaderMeComp.decode bytes
  let (massActionReportId, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (targetPartyIdSessionId, bytes) ← decodeUIntLE 4 bytes
  let (targetPartyIdExecutingTrader, bytes) ← decodeUIntLE 4 bytes
  let (partyIdEnteringTrader, bytes) ← decodeUIntLE 4 bytes
  let (noNotAffectedOrders, bytes) ← decodeUIntLE 2 bytes
  let (noAffectedOrderRequests, bytes) ← decodeUIntLE 2 bytes
  let (partyIdEnteringFirm, bytes) ← decodeUInt 1 bytes
  let (massActionReason, bytes) ← decodeUInt 1 bytes
  let (execInst, bytes) ← decodeUInt 1 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (notAffectedOrdersGrpComp_, bytes) ← decodeMany NotAffectedOrdersGrpComp.decode noNotAffectedOrders.toNat bytes
  let (affectedOrderRequestsGrpComp_, bytes) ← decodeMany AffectedOrderRequestsGrpComp.decode noAffectedOrderRequests.toNat bytes
  if fits_notAffectedOrdersGrpComp : notAffectedOrdersGrpComp_.length < 256 ^ 2 then
    if fits_affectedOrderRequestsGrpComp : affectedOrderRequestsGrpComp_.length < 256 ^ 2 then
      pure ({ pad2, rbcHeaderMeComp, massActionReportId, securityId, price, marketSegmentId, targetPartyIdSessionId, targetPartyIdExecutingTrader, partyIdEnteringTrader, partyIdEnteringFirm, massActionReason, execInst, side, notAffectedOrdersGrpComp := ⟨notAffectedOrdersGrpComp_, fits_notAffectedOrdersGrpComp⟩, affectedOrderRequestsGrpComp := ⟨affectedOrderRequestsGrpComp_, fits_affectedOrderRequestsGrpComp⟩ }, bytes)
    else none
  else none

theorem encode_length_pos (message : DeleteAllOrderBroadcast) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : DeleteAllOrderBroadcast) : (encode message).length ≤ 1572946 := by
  have bound_notAffectedOrdersGrpComp := message.notAffectedOrdersGrpComp.length_lt
  have bound_affectedOrderRequestsGrpComp := message.affectedOrderRequestsGrpComp.length_lt
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RbcHeaderMeComp.encode_length, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const NotAffectedOrdersGrpComp.encode 16 NotAffectedOrdersGrpComp.encode_length, encodeMany_length_const AffectedOrderRequestsGrpComp.encode 8 AffectedOrderRequestsGrpComp.encode_length]
  omega

@[simp] theorem decode_encode (message : DeleteAllOrderBroadcast) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [RbcHeaderMeComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 2 NotAffectedOrdersGrpComp.encode NotAffectedOrdersGrpComp.decode NotAffectedOrdersGrpComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 2 AffectedOrderRequestsGrpComp.encode AffectedOrderRequestsGrpComp.decode AffectedOrderRequestsGrpComp.decode_encode]
  simp only [Option.bind_some]
  simp only [message.notAffectedOrdersGrpComp.length_lt, message.affectedOrderRequestsGrpComp.length_lt, ↓reduceDIte]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : DeleteAllOrderBroadcast) : decode (encode message) = some (message, []) := by
  have trailing := decode_encode message []
  rw [List.append_nil] at trailing
  exact trailing

end DeleteAllOrderBroadcast

/-- Delete All Order Nr Response: 58 bytes -/
structure DeleteAllOrderNrResponse where
  pad2 : Alpha 2
  nrResponseHeaderMeComp : NrResponseHeaderMeComp
  massActionReportId : BitVec 64
  deriving DecidableEq, Repr

namespace DeleteAllOrderNrResponse

def encode (message : DeleteAllOrderNrResponse) : List UInt8 :=
  Alpha.encode message.pad2
    ++ NrResponseHeaderMeComp.encode message.nrResponseHeaderMeComp
    ++ encodeUIntLE 8 message.massActionReportId

def decode (bytes : List UInt8) : Option (DeleteAllOrderNrResponse × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (nrResponseHeaderMeComp, bytes) ← NrResponseHeaderMeComp.decode bytes
  let (massActionReportId, bytes) ← decodeUIntLE 8 bytes
  pure ({ pad2, nrResponseHeaderMeComp, massActionReportId }, bytes)

@[simp] theorem encode_length (message : DeleteAllOrderNrResponse) : (encode message).length = 58 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, NrResponseHeaderMeComp.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : DeleteAllOrderNrResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DeleteAllOrderNrResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [NrResponseHeaderMeComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : DeleteAllOrderNrResponse) : decode (encode message) = some (message, []) := by
  have trailing := decode_encode message []
  rw [List.append_nil] at trailing
  exact trailing

end DeleteAllOrderNrResponse

/-- Delete All Order Quote Event Broadcast: 82 bytes -/
structure DeleteAllOrderQuoteEventBroadcast where
  pad2 : Alpha 2
  rbcHeaderMeComp : RbcHeaderMeComp
  massActionReportId : BitVec 64
  securityId : BitVec 64
  marketSegmentId : BitVec 32
  massActionReason : BitVec 8
  execInst : BitVec 8
  pad2v2 : Alpha 2
  deriving DecidableEq, Repr

namespace DeleteAllOrderQuoteEventBroadcast

def encode (message : DeleteAllOrderQuoteEventBroadcast) : List UInt8 :=
  Alpha.encode message.pad2
    ++ RbcHeaderMeComp.encode message.rbcHeaderMeComp
    ++ encodeUIntLE 8 message.massActionReportId
    ++ encodeUIntLE 8 message.securityId
    ++ encodeUIntLE 4 message.marketSegmentId
    ++ encodeUInt 1 message.massActionReason
    ++ encodeUInt 1 message.execInst
    ++ Alpha.encode message.pad2v2

def decode (bytes : List UInt8) : Option (DeleteAllOrderQuoteEventBroadcast × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderMeComp, bytes) ← RbcHeaderMeComp.decode bytes
  let (massActionReportId, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (massActionReason, bytes) ← decodeUInt 1 bytes
  let (execInst, bytes) ← decodeUInt 1 bytes
  let (pad2v2, bytes) ← Alpha.decode 2 bytes
  pure ({ pad2, rbcHeaderMeComp, massActionReportId, securityId, marketSegmentId, massActionReason, execInst, pad2v2 }, bytes)

@[simp] theorem encode_length (message : DeleteAllOrderQuoteEventBroadcast) : (encode message).length = 82 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RbcHeaderMeComp.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : DeleteAllOrderQuoteEventBroadcast) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DeleteAllOrderQuoteEventBroadcast) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [RbcHeaderMeComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : DeleteAllOrderQuoteEventBroadcast) : decode (encode message) = some (message, []) := by
  have trailing := decode_encode message []
  rw [List.append_nil] at trailing
  exact trailing

end DeleteAllOrderQuoteEventBroadcast

/-- Response Header Me Comp: 64 bytes -/
structure ResponseHeaderMeComp where
  requestTime : BitVec 64
  trdRegTsTimeIn : BitVec 64
  trdRegTsTimeOut : BitVec 64
  responseIn : BitVec 64
  sendingTime : BitVec 64
  msgSeqNum : BitVec 32
  partitionId : BitVec 16
  applId : BitVec 8
  applMsgId : Alpha 16
  lastFragment : BitVec 8
  deriving DecidableEq, Repr

namespace ResponseHeaderMeComp

def encode (message : ResponseHeaderMeComp) : List UInt8 :=
  encodeUIntLE 8 message.requestTime
    ++ encodeUIntLE 8 message.trdRegTsTimeIn
    ++ encodeUIntLE 8 message.trdRegTsTimeOut
    ++ encodeUIntLE 8 message.responseIn
    ++ encodeUIntLE 8 message.sendingTime
    ++ encodeUIntLE 4 message.msgSeqNum
    ++ encodeUIntLE 2 message.partitionId
    ++ encodeUInt 1 message.applId
    ++ Alpha.encode message.applMsgId
    ++ encodeUInt 1 message.lastFragment

def decode (bytes : List UInt8) : Option (ResponseHeaderMeComp × List UInt8) := do
  let (requestTime, bytes) ← decodeUIntLE 8 bytes
  let (trdRegTsTimeIn, bytes) ← decodeUIntLE 8 bytes
  let (trdRegTsTimeOut, bytes) ← decodeUIntLE 8 bytes
  let (responseIn, bytes) ← decodeUIntLE 8 bytes
  let (sendingTime, bytes) ← decodeUIntLE 8 bytes
  let (msgSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (partitionId, bytes) ← decodeUIntLE 2 bytes
  let (applId, bytes) ← decodeUInt 1 bytes
  let (applMsgId, bytes) ← Alpha.decode 16 bytes
  let (lastFragment, bytes) ← decodeUInt 1 bytes
  pure ({ requestTime, trdRegTsTimeIn, trdRegTsTimeOut, responseIn, sendingTime, msgSeqNum, partitionId, applId, applMsgId, lastFragment }, bytes)

@[simp] theorem encode_length (message : ResponseHeaderMeComp) : (encode message).length = 64 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : ResponseHeaderMeComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ResponseHeaderMeComp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

end ResponseHeaderMeComp

/-- Delete All Order Response -/
structure DeleteAllOrderResponse where
  pad2 : Alpha 2
  responseHeaderMeComp : ResponseHeaderMeComp
  massActionReportId : BitVec 64
  pad4 : Alpha 4
  notAffectedOrdersGrpComp : Bounded 2 NotAffectedOrdersGrpComp
  affectedOrderRequestsGrpComp : Bounded 2 AffectedOrderRequestsGrpComp
  deriving DecidableEq, Repr

namespace DeleteAllOrderResponse

def encode (message : DeleteAllOrderResponse) : List UInt8 :=
  Alpha.encode message.pad2
    ++ ResponseHeaderMeComp.encode message.responseHeaderMeComp
    ++ encodeUIntLE 8 message.massActionReportId
    ++ encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.notAffectedOrdersGrpComp.val.length)
    ++ encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.affectedOrderRequestsGrpComp.val.length)
    ++ Alpha.encode message.pad4
    ++ encodeMany NotAffectedOrdersGrpComp.encode message.notAffectedOrdersGrpComp.val
    ++ encodeMany AffectedOrderRequestsGrpComp.encode message.affectedOrderRequestsGrpComp.val

def decode (bytes : List UInt8) : Option (DeleteAllOrderResponse × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (responseHeaderMeComp, bytes) ← ResponseHeaderMeComp.decode bytes
  let (massActionReportId, bytes) ← decodeUIntLE 8 bytes
  let (noNotAffectedOrders, bytes) ← decodeUIntLE 2 bytes
  let (noAffectedOrderRequests, bytes) ← decodeUIntLE 2 bytes
  let (pad4, bytes) ← Alpha.decode 4 bytes
  let (notAffectedOrdersGrpComp_, bytes) ← decodeMany NotAffectedOrdersGrpComp.decode noNotAffectedOrders.toNat bytes
  let (affectedOrderRequestsGrpComp_, bytes) ← decodeMany AffectedOrderRequestsGrpComp.decode noAffectedOrderRequests.toNat bytes
  if fits_notAffectedOrdersGrpComp : notAffectedOrdersGrpComp_.length < 256 ^ 2 then
    if fits_affectedOrderRequestsGrpComp : affectedOrderRequestsGrpComp_.length < 256 ^ 2 then
      pure ({ pad2, responseHeaderMeComp, massActionReportId, pad4, notAffectedOrdersGrpComp := ⟨notAffectedOrdersGrpComp_, fits_notAffectedOrdersGrpComp⟩, affectedOrderRequestsGrpComp := ⟨affectedOrderRequestsGrpComp_, fits_affectedOrderRequestsGrpComp⟩ }, bytes)
    else none
  else none

theorem encode_length_pos (message : DeleteAllOrderResponse) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : DeleteAllOrderResponse) : (encode message).length ≤ 1572922 := by
  have bound_notAffectedOrdersGrpComp := message.notAffectedOrdersGrpComp.length_lt
  have bound_affectedOrderRequestsGrpComp := message.affectedOrderRequestsGrpComp.length_lt
  unfold encode
  simp only [List.length_append, Alpha.encode_length, ResponseHeaderMeComp.encode_length, encodeUIntLE_length, encodeMany_length_const NotAffectedOrdersGrpComp.encode 16 NotAffectedOrdersGrpComp.encode_length, encodeMany_length_const AffectedOrderRequestsGrpComp.encode 8 AffectedOrderRequestsGrpComp.encode_length]
  omega

@[simp] theorem decode_encode (message : DeleteAllOrderResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [ResponseHeaderMeComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 2 NotAffectedOrdersGrpComp.encode NotAffectedOrdersGrpComp.decode NotAffectedOrdersGrpComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 2 AffectedOrderRequestsGrpComp.encode AffectedOrderRequestsGrpComp.decode AffectedOrderRequestsGrpComp.decode_encode]
  simp only [Option.bind_some]
  simp only [message.notAffectedOrdersGrpComp.length_lt, message.affectedOrderRequestsGrpComp.length_lt, ↓reduceDIte]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : DeleteAllOrderResponse) : decode (encode message) = some (message, []) := by
  have trailing := decode_encode message []
  rw [List.append_nil] at trailing
  exact trailing

end DeleteAllOrderResponse

/-- Not Affected Securities Grp Comp: 8 bytes -/
structure NotAffectedSecuritiesGrpComp where
  notAffectedSecurityId : BitVec 64
  deriving DecidableEq, Repr

namespace NotAffectedSecuritiesGrpComp

def encode (message : NotAffectedSecuritiesGrpComp) : List UInt8 :=
  encodeUIntLE 8 message.notAffectedSecurityId

def decode (bytes : List UInt8) : Option (NotAffectedSecuritiesGrpComp × List UInt8) := do
  let (notAffectedSecurityId, bytes) ← decodeUIntLE 8 bytes
  pure ({ notAffectedSecurityId }, bytes)

@[simp] theorem encode_length (message : NotAffectedSecuritiesGrpComp) : (encode message).length = 8 := by
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : NotAffectedSecuritiesGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NotAffectedSecuritiesGrpComp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

end NotAffectedSecuritiesGrpComp

/-- Delete All Quote Broadcast -/
structure DeleteAllQuoteBroadcast where
  pad2 : Alpha 2
  rbcHeaderMeComp : RbcHeaderMeComp
  massActionReportId : BitVec 64
  securityId : BitVec 64
  marketSegmentId : BitVec 32
  targetPartyIdSessionId : BitVec 32
  partyIdEnteringTrader : BitVec 32
  targetPartyIdExecutingTrader : BitVec 32
  massActionReason : BitVec 8
  partyIdEnteringFirm : BitVec 8
  targetPartyIdDeskId : Alpha 3
  pad1 : Alpha 1
  notAffectedSecuritiesGrpComp : Bounded 2 NotAffectedSecuritiesGrpComp
  deriving DecidableEq, Repr

namespace DeleteAllQuoteBroadcast

def encode (message : DeleteAllQuoteBroadcast) : List UInt8 :=
  Alpha.encode message.pad2
    ++ RbcHeaderMeComp.encode message.rbcHeaderMeComp
    ++ encodeUIntLE 8 message.massActionReportId
    ++ encodeUIntLE 8 message.securityId
    ++ encodeUIntLE 4 message.marketSegmentId
    ++ encodeUIntLE 4 message.targetPartyIdSessionId
    ++ encodeUIntLE 4 message.partyIdEnteringTrader
    ++ encodeUIntLE 4 message.targetPartyIdExecutingTrader
    ++ encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.notAffectedSecuritiesGrpComp.val.length)
    ++ encodeUInt 1 message.massActionReason
    ++ encodeUInt 1 message.partyIdEnteringFirm
    ++ Alpha.encode message.targetPartyIdDeskId
    ++ Alpha.encode message.pad1
    ++ encodeMany NotAffectedSecuritiesGrpComp.encode message.notAffectedSecuritiesGrpComp.val

def decode (bytes : List UInt8) : Option (DeleteAllQuoteBroadcast × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderMeComp, bytes) ← RbcHeaderMeComp.decode bytes
  let (massActionReportId, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (targetPartyIdSessionId, bytes) ← decodeUIntLE 4 bytes
  let (partyIdEnteringTrader, bytes) ← decodeUIntLE 4 bytes
  let (targetPartyIdExecutingTrader, bytes) ← decodeUIntLE 4 bytes
  let (noNotAffectedSecurities, bytes) ← decodeUIntLE 2 bytes
  let (massActionReason, bytes) ← decodeUInt 1 bytes
  let (partyIdEnteringFirm, bytes) ← decodeUInt 1 bytes
  let (targetPartyIdDeskId, bytes) ← Alpha.decode 3 bytes
  let (pad1, bytes) ← Alpha.decode 1 bytes
  let (notAffectedSecuritiesGrpComp_, bytes) ← decodeMany NotAffectedSecuritiesGrpComp.decode noNotAffectedSecurities.toNat bytes
  if fits_notAffectedSecuritiesGrpComp : notAffectedSecuritiesGrpComp_.length < 256 ^ 2 then
    pure ({ pad2, rbcHeaderMeComp, massActionReportId, securityId, marketSegmentId, targetPartyIdSessionId, partyIdEnteringTrader, targetPartyIdExecutingTrader, massActionReason, partyIdEnteringFirm, targetPartyIdDeskId, pad1, notAffectedSecuritiesGrpComp := ⟨notAffectedSecuritiesGrpComp_, fits_notAffectedSecuritiesGrpComp⟩ }, bytes)
  else none

theorem encode_length_pos (message : DeleteAllQuoteBroadcast) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : DeleteAllQuoteBroadcast) : (encode message).length ≤ 524378 := by
  have bound_notAffectedSecuritiesGrpComp := message.notAffectedSecuritiesGrpComp.length_lt
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RbcHeaderMeComp.encode_length, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const NotAffectedSecuritiesGrpComp.encode 8 NotAffectedSecuritiesGrpComp.encode_length]
  omega

@[simp] theorem decode_encode (message : DeleteAllQuoteBroadcast) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [RbcHeaderMeComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 2 NotAffectedSecuritiesGrpComp.encode NotAffectedSecuritiesGrpComp.decode NotAffectedSecuritiesGrpComp.decode_encode]
  simp only [Option.bind_some]
  simp only [message.notAffectedSecuritiesGrpComp.length_lt, ↓reduceDIte]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : DeleteAllQuoteBroadcast) : decode (encode message) = some (message, []) := by
  have trailing := decode_encode message []
  rw [List.append_nil] at trailing
  exact trailing

end DeleteAllQuoteBroadcast

/-- Delete All Quote Response -/
structure DeleteAllQuoteResponse where
  pad2 : Alpha 2
  nrResponseHeaderMeComp : NrResponseHeaderMeComp
  massActionReportId : BitVec 64
  pad6 : Alpha 6
  notAffectedSecuritiesGrpComp : Bounded 2 NotAffectedSecuritiesGrpComp
  deriving DecidableEq, Repr

namespace DeleteAllQuoteResponse

def encode (message : DeleteAllQuoteResponse) : List UInt8 :=
  Alpha.encode message.pad2
    ++ NrResponseHeaderMeComp.encode message.nrResponseHeaderMeComp
    ++ encodeUIntLE 8 message.massActionReportId
    ++ encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.notAffectedSecuritiesGrpComp.val.length)
    ++ Alpha.encode message.pad6
    ++ encodeMany NotAffectedSecuritiesGrpComp.encode message.notAffectedSecuritiesGrpComp.val

def decode (bytes : List UInt8) : Option (DeleteAllQuoteResponse × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (nrResponseHeaderMeComp, bytes) ← NrResponseHeaderMeComp.decode bytes
  let (massActionReportId, bytes) ← decodeUIntLE 8 bytes
  let (noNotAffectedSecurities, bytes) ← decodeUIntLE 2 bytes
  let (pad6, bytes) ← Alpha.decode 6 bytes
  let (notAffectedSecuritiesGrpComp_, bytes) ← decodeMany NotAffectedSecuritiesGrpComp.decode noNotAffectedSecurities.toNat bytes
  if fits_notAffectedSecuritiesGrpComp : notAffectedSecuritiesGrpComp_.length < 256 ^ 2 then
    pure ({ pad2, nrResponseHeaderMeComp, massActionReportId, pad6, notAffectedSecuritiesGrpComp := ⟨notAffectedSecuritiesGrpComp_, fits_notAffectedSecuritiesGrpComp⟩ }, bytes)
  else none

theorem encode_length_pos (message : DeleteAllQuoteResponse) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : DeleteAllQuoteResponse) : (encode message).length ≤ 524346 := by
  have bound_notAffectedSecuritiesGrpComp := message.notAffectedSecuritiesGrpComp.length_lt
  unfold encode
  simp only [List.length_append, Alpha.encode_length, NrResponseHeaderMeComp.encode_length, encodeUIntLE_length, encodeMany_length_const NotAffectedSecuritiesGrpComp.encode 8 NotAffectedSecuritiesGrpComp.encode_length]
  omega

@[simp] theorem decode_encode (message : DeleteAllQuoteResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [NrResponseHeaderMeComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 2 NotAffectedSecuritiesGrpComp.encode NotAffectedSecuritiesGrpComp.decode NotAffectedSecuritiesGrpComp.decode_encode]
  simp only [Option.bind_some]
  simp only [message.notAffectedSecuritiesGrpComp.length_lt, ↓reduceDIte]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : DeleteAllQuoteResponse) : decode (encode message) = some (message, []) := by
  have trailing := decode_encode message []
  rw [List.append_nil] at trailing
  exact trailing

end DeleteAllQuoteResponse

/-- Delete Order Broadcast: 154 bytes -/
structure DeleteOrderBroadcast where
  pad2 : Alpha 2
  rbcHeaderMeComp : RbcHeaderMeComp
  orderId : BitVec 64
  clOrdId : BitVec 64
  origClOrdId : BitVec 64
  securityId : BitVec 64
  execId : BitVec 64
  cumQty : BitVec 64
  cxlQty : BitVec 64
  marketSegmentId : BitVec 32
  partyIdEnteringTrader : BitVec 32
  partyIdSessionId : BitVec 32
  execRestatementReason : BitVec 16
  partyIdEnteringFirm : BitVec 8
  ordStatus : OrdStatus
  execType : ExecType
  productComplex : BitVec 8
  side : BitVec 8
  fixClOrdId : Alpha 20
  pad1 : Alpha 1
  deriving DecidableEq, Repr

namespace DeleteOrderBroadcast

def encode (message : DeleteOrderBroadcast) : List UInt8 :=
  Alpha.encode message.pad2
    ++ RbcHeaderMeComp.encode message.rbcHeaderMeComp
    ++ encodeUIntLE 8 message.orderId
    ++ encodeUIntLE 8 message.clOrdId
    ++ encodeUIntLE 8 message.origClOrdId
    ++ encodeUIntLE 8 message.securityId
    ++ encodeUIntLE 8 message.execId
    ++ encodeUIntLE 8 message.cumQty
    ++ encodeUIntLE 8 message.cxlQty
    ++ encodeUIntLE 4 message.marketSegmentId
    ++ encodeUIntLE 4 message.partyIdEnteringTrader
    ++ encodeUIntLE 4 message.partyIdSessionId
    ++ encodeUIntLE 2 message.execRestatementReason
    ++ encodeUInt 1 message.partyIdEnteringFirm
    ++ OrdStatus.encode message.ordStatus
    ++ ExecType.encode message.execType
    ++ encodeUInt 1 message.productComplex
    ++ encodeUInt 1 message.side
    ++ Alpha.encode message.fixClOrdId
    ++ Alpha.encode message.pad1

def decode (bytes : List UInt8) : Option (DeleteOrderBroadcast × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderMeComp, bytes) ← RbcHeaderMeComp.decode bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (origClOrdId, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  let (cumQty, bytes) ← decodeUIntLE 8 bytes
  let (cxlQty, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (partyIdEnteringTrader, bytes) ← decodeUIntLE 4 bytes
  let (partyIdSessionId, bytes) ← decodeUIntLE 4 bytes
  let (execRestatementReason, bytes) ← decodeUIntLE 2 bytes
  let (partyIdEnteringFirm, bytes) ← decodeUInt 1 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (productComplex, bytes) ← decodeUInt 1 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (fixClOrdId, bytes) ← Alpha.decode 20 bytes
  let (pad1, bytes) ← Alpha.decode 1 bytes
  pure ({ pad2, rbcHeaderMeComp, orderId, clOrdId, origClOrdId, securityId, execId, cumQty, cxlQty, marketSegmentId, partyIdEnteringTrader, partyIdSessionId, execRestatementReason, partyIdEnteringFirm, ordStatus, execType, productComplex, side, fixClOrdId, pad1 }, bytes)

@[simp] theorem encode_length (message : DeleteOrderBroadcast) : (encode message).length = 154 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RbcHeaderMeComp.encode_length, encodeUIntLE_length, encodeUInt_length, OrdStatus.encode_length, ExecType.encode_length]

theorem encode_length_pos (message : DeleteOrderBroadcast) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DeleteOrderBroadcast) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [RbcHeaderMeComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [OrdStatus.decode_encode]
  simp only [Option.bind_some]
  rw [ExecType.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : DeleteOrderBroadcast) : decode (encode message) = some (message, []) := by
  have trailing := decode_encode message []
  rw [List.append_nil] at trailing
  exact trailing

end DeleteOrderBroadcast

/-- Delete Order Nr Response: 114 bytes -/
structure DeleteOrderNrResponse where
  pad2 : Alpha 2
  nrResponseHeaderMeComp : NrResponseHeaderMeComp
  orderId : BitVec 64
  clOrdId : BitVec 64
  origClOrdId : BitVec 64
  securityId : BitVec 64
  execId : BitVec 64
  cumQty : BitVec 64
  cxlQty : BitVec 64
  ordStatus : OrdStatus
  execType : ExecType
  execRestatementReason : BitVec 16
  productComplex : BitVec 8
  transactionDelayIndicator : BitVec 8
  pad2v2 : Alpha 2
  deriving DecidableEq, Repr

namespace DeleteOrderNrResponse

def encode (message : DeleteOrderNrResponse) : List UInt8 :=
  Alpha.encode message.pad2
    ++ NrResponseHeaderMeComp.encode message.nrResponseHeaderMeComp
    ++ encodeUIntLE 8 message.orderId
    ++ encodeUIntLE 8 message.clOrdId
    ++ encodeUIntLE 8 message.origClOrdId
    ++ encodeUIntLE 8 message.securityId
    ++ encodeUIntLE 8 message.execId
    ++ encodeUIntLE 8 message.cumQty
    ++ encodeUIntLE 8 message.cxlQty
    ++ OrdStatus.encode message.ordStatus
    ++ ExecType.encode message.execType
    ++ encodeUIntLE 2 message.execRestatementReason
    ++ encodeUInt 1 message.productComplex
    ++ encodeUInt 1 message.transactionDelayIndicator
    ++ Alpha.encode message.pad2v2

def decode (bytes : List UInt8) : Option (DeleteOrderNrResponse × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (nrResponseHeaderMeComp, bytes) ← NrResponseHeaderMeComp.decode bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (origClOrdId, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  let (cumQty, bytes) ← decodeUIntLE 8 bytes
  let (cxlQty, bytes) ← decodeUIntLE 8 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (execRestatementReason, bytes) ← decodeUIntLE 2 bytes
  let (productComplex, bytes) ← decodeUInt 1 bytes
  let (transactionDelayIndicator, bytes) ← decodeUInt 1 bytes
  let (pad2v2, bytes) ← Alpha.decode 2 bytes
  pure ({ pad2, nrResponseHeaderMeComp, orderId, clOrdId, origClOrdId, securityId, execId, cumQty, cxlQty, ordStatus, execType, execRestatementReason, productComplex, transactionDelayIndicator, pad2v2 }, bytes)

@[simp] theorem encode_length (message : DeleteOrderNrResponse) : (encode message).length = 114 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, NrResponseHeaderMeComp.encode_length, encodeUIntLE_length, OrdStatus.encode_length, ExecType.encode_length, encodeUInt_length]

theorem encode_length_pos (message : DeleteOrderNrResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DeleteOrderNrResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [NrResponseHeaderMeComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [OrdStatus.decode_encode]
  simp only [Option.bind_some]
  rw [ExecType.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : DeleteOrderNrResponse) : decode (encode message) = some (message, []) := by
  have trailing := decode_encode message []
  rw [List.append_nil] at trailing
  exact trailing

end DeleteOrderNrResponse

/-- Delete Order Response: 130 bytes -/
structure DeleteOrderResponse where
  pad2 : Alpha 2
  responseHeaderMeComp : ResponseHeaderMeComp
  orderId : BitVec 64
  clOrdId : BitVec 64
  origClOrdId : BitVec 64
  securityId : BitVec 64
  execId : BitVec 64
  cumQty : BitVec 64
  cxlQty : BitVec 64
  ordStatus : OrdStatus
  execType : ExecType
  execRestatementReason : BitVec 16
  productComplex : BitVec 8
  transactionDelayIndicator : BitVec 8
  pad2v2 : Alpha 2
  deriving DecidableEq, Repr

namespace DeleteOrderResponse

def encode (message : DeleteOrderResponse) : List UInt8 :=
  Alpha.encode message.pad2
    ++ ResponseHeaderMeComp.encode message.responseHeaderMeComp
    ++ encodeUIntLE 8 message.orderId
    ++ encodeUIntLE 8 message.clOrdId
    ++ encodeUIntLE 8 message.origClOrdId
    ++ encodeUIntLE 8 message.securityId
    ++ encodeUIntLE 8 message.execId
    ++ encodeUIntLE 8 message.cumQty
    ++ encodeUIntLE 8 message.cxlQty
    ++ OrdStatus.encode message.ordStatus
    ++ ExecType.encode message.execType
    ++ encodeUIntLE 2 message.execRestatementReason
    ++ encodeUInt 1 message.productComplex
    ++ encodeUInt 1 message.transactionDelayIndicator
    ++ Alpha.encode message.pad2v2

def decode (bytes : List UInt8) : Option (DeleteOrderResponse × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (responseHeaderMeComp, bytes) ← ResponseHeaderMeComp.decode bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (origClOrdId, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  let (cumQty, bytes) ← decodeUIntLE 8 bytes
  let (cxlQty, bytes) ← decodeUIntLE 8 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (execRestatementReason, bytes) ← decodeUIntLE 2 bytes
  let (productComplex, bytes) ← decodeUInt 1 bytes
  let (transactionDelayIndicator, bytes) ← decodeUInt 1 bytes
  let (pad2v2, bytes) ← Alpha.decode 2 bytes
  pure ({ pad2, responseHeaderMeComp, orderId, clOrdId, origClOrdId, securityId, execId, cumQty, cxlQty, ordStatus, execType, execRestatementReason, productComplex, transactionDelayIndicator, pad2v2 }, bytes)

@[simp] theorem encode_length (message : DeleteOrderResponse) : (encode message).length = 130 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, ResponseHeaderMeComp.encode_length, encodeUIntLE_length, OrdStatus.encode_length, ExecType.encode_length, encodeUInt_length]

theorem encode_length_pos (message : DeleteOrderResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DeleteOrderResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [ResponseHeaderMeComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [OrdStatus.decode_encode]
  simp only [Option.bind_some]
  rw [ExecType.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : DeleteOrderResponse) : decode (encode message) = some (message, []) := by
  have trailing := decode_encode message []
  rw [List.append_nil] at trailing
  exact trailing

end DeleteOrderResponse

/-- Forced Logout Notification -/
structure ForcedLogoutNotification where
  pad2 : Alpha 2
  notifHeaderComp : NotifHeaderComp
  varText : Bounded 2 UInt8
  alignmentPadding : Capped 4282374239
  deriving DecidableEq, Repr

namespace ForcedLogoutNotification

def encode (message : ForcedLogoutNotification) : List UInt8 :=
  Alpha.encode message.pad2
    ++ NotifHeaderComp.encode message.notifHeaderComp
    ++ encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.varText.val.length)
    ++ encodeMany Byte.encode message.varText.val
    ++ message.alignmentPadding.val

def decode (bytes : List UInt8) : Option ForcedLogoutNotification := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (notifHeaderComp, bytes) ← NotifHeaderComp.decode bytes
  let (varTextLen, bytes) ← decodeUIntLE 2 bytes
  let (varText_, bytes) ← decodeMany Byte.decode varTextLen.toNat bytes
  let alignmentPadding_ := bytes
  if fits_varText : varText_.length < 256 ^ 2 then
    if fits_alignmentPadding : alignmentPadding_.length ≤ 4282374239 then
      pure { pad2, notifHeaderComp, varText := ⟨varText_, fits_varText⟩, alignmentPadding := ⟨alignmentPadding_, fits_alignmentPadding⟩ }
    else none
  else none

theorem encode_length_pos (message : ForcedLogoutNotification) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ForcedLogoutNotification) : (encode message).length ≤ 4282439786 := by
  have bound_varText := message.varText.length_lt
  have bound_alignmentPadding := message.alignmentPadding.length_le
  unfold encode
  simp only [List.length_append, Alpha.encode_length, NotifHeaderComp.encode_length, encodeUIntLE_length, encodeMany_length_const Byte.encode 1 Byte.encode_length]
  omega

theorem decode_encode (message : ForcedLogoutNotification) : decode (encode message) = some message := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [NotifHeaderComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 2 Byte.encode Byte.decode Byte.decode_encode]
  simp only [Option.bind_some]
  simp only [message.varText.length_lt, message.alignmentPadding.length_le, ↓reduceDIte]
  rfl

end ForcedLogoutNotification

/-- Forced User Logout Notification -/
structure ForcedUserLogoutNotification where
  pad2 : Alpha 2
  notifHeaderComp : NotifHeaderComp
  username : BitVec 32
  userStatus : BitVec 8
  varText : Bounded 2 UInt8
  alignmentPadding : Capped 4282374239
  deriving DecidableEq, Repr

namespace ForcedUserLogoutNotification

def encode (message : ForcedUserLogoutNotification) : List UInt8 :=
  Alpha.encode message.pad2
    ++ NotifHeaderComp.encode message.notifHeaderComp
    ++ encodeUIntLE 4 message.username
    ++ encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.varText.val.length)
    ++ encodeUInt 1 message.userStatus
    ++ encodeMany Byte.encode message.varText.val
    ++ message.alignmentPadding.val

def decode (bytes : List UInt8) : Option ForcedUserLogoutNotification := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (notifHeaderComp, bytes) ← NotifHeaderComp.decode bytes
  let (username, bytes) ← decodeUIntLE 4 bytes
  let (varTextLen, bytes) ← decodeUIntLE 2 bytes
  let (userStatus, bytes) ← decodeUInt 1 bytes
  let (varText_, bytes) ← decodeMany Byte.decode varTextLen.toNat bytes
  let alignmentPadding_ := bytes
  if fits_varText : varText_.length < 256 ^ 2 then
    if fits_alignmentPadding : alignmentPadding_.length ≤ 4282374239 then
      pure { pad2, notifHeaderComp, username, userStatus, varText := ⟨varText_, fits_varText⟩, alignmentPadding := ⟨alignmentPadding_, fits_alignmentPadding⟩ }
    else none
  else none

theorem encode_length_pos (message : ForcedUserLogoutNotification) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ForcedUserLogoutNotification) : (encode message).length ≤ 4282439791 := by
  have bound_varText := message.varText.length_lt
  have bound_alignmentPadding := message.alignmentPadding.length_le
  unfold encode
  simp only [List.length_append, Alpha.encode_length, NotifHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const Byte.encode 1 Byte.encode_length]
  omega

theorem decode_encode (message : ForcedUserLogoutNotification) : decode (encode message) = some message := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [NotifHeaderComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 2 Byte.encode Byte.decode Byte.decode_encode]
  simp only [Option.bind_some]
  simp only [message.varText.length_lt, message.alignmentPadding.length_le, ↓reduceDIte]
  rfl

end ForcedUserLogoutNotification

/-- Heartbeat Notification: 10 bytes -/
structure HeartbeatNotification where
  pad2 : Alpha 2
  notifHeaderComp : NotifHeaderComp
  deriving DecidableEq, Repr

namespace HeartbeatNotification

def encode (message : HeartbeatNotification) : List UInt8 :=
  Alpha.encode message.pad2
    ++ NotifHeaderComp.encode message.notifHeaderComp

def decode (bytes : List UInt8) : Option (HeartbeatNotification × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (notifHeaderComp, bytes) ← NotifHeaderComp.decode bytes
  pure ({ pad2, notifHeaderComp }, bytes)

@[simp] theorem encode_length (message : HeartbeatNotification) : (encode message).length = 10 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, NotifHeaderComp.encode_length]

theorem encode_length_pos (message : HeartbeatNotification) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : HeartbeatNotification) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [NotifHeaderComp.decode_encode, Option.bind_some]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : HeartbeatNotification) : decode (encode message) = some (message, []) := by
  have trailing := decode_encode message []
  rw [List.append_nil] at trailing
  exact trailing

end HeartbeatNotification

/-- Enrichment Rules Grp Comp: 104 bytes -/
structure EnrichmentRulesGrpComp where
  partyIdSponsoredAccessUnit : BitVec 32
  enrichmentRuleId : BitVec 16
  partyIdOriginationMarket : BitVec 8
  account : Alpha 2
  positionEffect : PositionEffect
  partyIdTakeUpTradingFirm : Alpha 5
  partyIdOrderOriginationFirm : Alpha 7
  partyIdBeneficiary : Alpha 9
  partySponsoredAccessUnit : Alpha 30
  freeText1 : Alpha 12
  freeText2 : Alpha 12
  freeText3 : Alpha 12
  pad7 : Alpha 7
  deriving DecidableEq, Repr

namespace EnrichmentRulesGrpComp

def encode (message : EnrichmentRulesGrpComp) : List UInt8 :=
  encodeUIntLE 4 message.partyIdSponsoredAccessUnit
    ++ encodeUIntLE 2 message.enrichmentRuleId
    ++ encodeUInt 1 message.partyIdOriginationMarket
    ++ Alpha.encode message.account
    ++ PositionEffect.encode message.positionEffect
    ++ Alpha.encode message.partyIdTakeUpTradingFirm
    ++ Alpha.encode message.partyIdOrderOriginationFirm
    ++ Alpha.encode message.partyIdBeneficiary
    ++ Alpha.encode message.partySponsoredAccessUnit
    ++ Alpha.encode message.freeText1
    ++ Alpha.encode message.freeText2
    ++ Alpha.encode message.freeText3
    ++ Alpha.encode message.pad7

def decode (bytes : List UInt8) : Option (EnrichmentRulesGrpComp × List UInt8) := do
  let (partyIdSponsoredAccessUnit, bytes) ← decodeUIntLE 4 bytes
  let (enrichmentRuleId, bytes) ← decodeUIntLE 2 bytes
  let (partyIdOriginationMarket, bytes) ← decodeUInt 1 bytes
  let (account, bytes) ← Alpha.decode 2 bytes
  let (positionEffect, bytes) ← PositionEffect.decode bytes
  let (partyIdTakeUpTradingFirm, bytes) ← Alpha.decode 5 bytes
  let (partyIdOrderOriginationFirm, bytes) ← Alpha.decode 7 bytes
  let (partyIdBeneficiary, bytes) ← Alpha.decode 9 bytes
  let (partySponsoredAccessUnit, bytes) ← Alpha.decode 30 bytes
  let (freeText1, bytes) ← Alpha.decode 12 bytes
  let (freeText2, bytes) ← Alpha.decode 12 bytes
  let (freeText3, bytes) ← Alpha.decode 12 bytes
  let (pad7, bytes) ← Alpha.decode 7 bytes
  pure ({ partyIdSponsoredAccessUnit, enrichmentRuleId, partyIdOriginationMarket, account, positionEffect, partyIdTakeUpTradingFirm, partyIdOrderOriginationFirm, partyIdBeneficiary, partySponsoredAccessUnit, freeText1, freeText2, freeText3, pad7 }, bytes)

@[simp] theorem encode_length (message : EnrichmentRulesGrpComp) : (encode message).length = 104 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length, PositionEffect.encode_length]

theorem encode_length_pos (message : EnrichmentRulesGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EnrichmentRulesGrpComp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [PositionEffect.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end EnrichmentRulesGrpComp

/-- Inquire Enrichment Rule Id List Response -/
structure InquireEnrichmentRuleIdListResponse where
  pad2 : Alpha 2
  responseHeaderComp : ResponseHeaderComp
  lastEntityProcessed : Alpha 16
  pad6 : Alpha 6
  enrichmentRulesGrpComp : Bounded 2 EnrichmentRulesGrpComp
  deriving DecidableEq, Repr

namespace InquireEnrichmentRuleIdListResponse

def encode (message : InquireEnrichmentRuleIdListResponse) : List UInt8 :=
  Alpha.encode message.pad2
    ++ ResponseHeaderComp.encode message.responseHeaderComp
    ++ Alpha.encode message.lastEntityProcessed
    ++ encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.enrichmentRulesGrpComp.val.length)
    ++ Alpha.encode message.pad6
    ++ encodeMany EnrichmentRulesGrpComp.encode message.enrichmentRulesGrpComp.val

def decode (bytes : List UInt8) : Option (InquireEnrichmentRuleIdListResponse × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (responseHeaderComp, bytes) ← ResponseHeaderComp.decode bytes
  let (lastEntityProcessed, bytes) ← Alpha.decode 16 bytes
  let (noEnrichmentRules, bytes) ← decodeUIntLE 2 bytes
  let (pad6, bytes) ← Alpha.decode 6 bytes
  let (enrichmentRulesGrpComp_, bytes) ← decodeMany EnrichmentRulesGrpComp.decode noEnrichmentRules.toNat bytes
  if fits_enrichmentRulesGrpComp : enrichmentRulesGrpComp_.length < 256 ^ 2 then
    pure ({ pad2, responseHeaderComp, lastEntityProcessed, pad6, enrichmentRulesGrpComp := ⟨enrichmentRulesGrpComp_, fits_enrichmentRulesGrpComp⟩ }, bytes)
  else none

theorem encode_length_pos (message : InquireEnrichmentRuleIdListResponse) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : InquireEnrichmentRuleIdListResponse) : (encode message).length ≤ 6815690 := by
  have bound_enrichmentRulesGrpComp := message.enrichmentRulesGrpComp.length_lt
  unfold encode
  simp only [List.length_append, Alpha.encode_length, ResponseHeaderComp.encode_length, encodeUIntLE_length, encodeMany_length_const EnrichmentRulesGrpComp.encode 104 EnrichmentRulesGrpComp.encode_length]
  omega

@[simp] theorem decode_encode (message : InquireEnrichmentRuleIdListResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [ResponseHeaderComp.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 2 EnrichmentRulesGrpComp.encode EnrichmentRulesGrpComp.decode EnrichmentRulesGrpComp.decode_encode]
  simp only [Option.bind_some]
  simp only [message.enrichmentRulesGrpComp.length_lt, ↓reduceDIte]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : InquireEnrichmentRuleIdListResponse) : decode (encode message) = some (message, []) := by
  have trailing := decode_encode message []
  rw [List.append_nil] at trailing
  exact trailing

end InquireEnrichmentRuleIdListResponse

/-- Mm Parameter Grp Comp: 48 bytes -/
structure MmParameterGrpComp where
  exposureDuration : BitVec 64
  cumQty : BitVec 64
  delta : BitVec 64
  vega : BitVec 64
  pctCount : BitVec 32
  targetPartyIdSessionId : BitVec 32
  mmRiskLimitActionType : BitVec 8
  pad7 : Alpha 7
  deriving DecidableEq, Repr

namespace MmParameterGrpComp

def encode (message : MmParameterGrpComp) : List UInt8 :=
  encodeUIntLE 8 message.exposureDuration
    ++ encodeUIntLE 8 message.cumQty
    ++ encodeUIntLE 8 message.delta
    ++ encodeUIntLE 8 message.vega
    ++ encodeUIntLE 4 message.pctCount
    ++ encodeUIntLE 4 message.targetPartyIdSessionId
    ++ encodeUInt 1 message.mmRiskLimitActionType
    ++ Alpha.encode message.pad7

def decode (bytes : List UInt8) : Option (MmParameterGrpComp × List UInt8) := do
  let (exposureDuration, bytes) ← decodeUIntLE 8 bytes
  let (cumQty, bytes) ← decodeUIntLE 8 bytes
  let (delta, bytes) ← decodeUIntLE 8 bytes
  let (vega, bytes) ← decodeUIntLE 8 bytes
  let (pctCount, bytes) ← decodeUIntLE 4 bytes
  let (targetPartyIdSessionId, bytes) ← decodeUIntLE 4 bytes
  let (mmRiskLimitActionType, bytes) ← decodeUInt 1 bytes
  let (pad7, bytes) ← Alpha.decode 7 bytes
  pure ({ exposureDuration, cumQty, delta, vega, pctCount, targetPartyIdSessionId, mmRiskLimitActionType, pad7 }, bytes)

@[simp] theorem encode_length (message : MmParameterGrpComp) : (encode message).length = 48 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : MmParameterGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MmParameterGrpComp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end MmParameterGrpComp

/-- Inquire Mm Parameter Response -/
structure InquireMmParameterResponse where
  pad2 : Alpha 2
  nrResponseHeaderMeComp : NrResponseHeaderMeComp
  mmParameterReportId : BitVec 64
  marketSegmentId : BitVec 32
  pad3 : Alpha 3
  mmParameterGrpComp : Bounded 1 MmParameterGrpComp
  deriving DecidableEq, Repr

namespace InquireMmParameterResponse

def encode (message : InquireMmParameterResponse) : List UInt8 :=
  Alpha.encode message.pad2
    ++ NrResponseHeaderMeComp.encode message.nrResponseHeaderMeComp
    ++ encodeUIntLE 8 message.mmParameterReportId
    ++ encodeUIntLE 4 message.marketSegmentId
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.mmParameterGrpComp.val.length)
    ++ Alpha.encode message.pad3
    ++ encodeMany MmParameterGrpComp.encode message.mmParameterGrpComp.val

def decode (bytes : List UInt8) : Option (InquireMmParameterResponse × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (nrResponseHeaderMeComp, bytes) ← NrResponseHeaderMeComp.decode bytes
  let (mmParameterReportId, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (noMmParameters, bytes) ← decodeUInt 1 bytes
  let (pad3, bytes) ← Alpha.decode 3 bytes
  let (mmParameterGrpComp_, bytes) ← decodeMany MmParameterGrpComp.decode noMmParameters.toNat bytes
  if fits_mmParameterGrpComp : mmParameterGrpComp_.length < 256 ^ 1 then
    pure ({ pad2, nrResponseHeaderMeComp, mmParameterReportId, marketSegmentId, pad3, mmParameterGrpComp := ⟨mmParameterGrpComp_, fits_mmParameterGrpComp⟩ }, bytes)
  else none

theorem encode_length_pos (message : InquireMmParameterResponse) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : InquireMmParameterResponse) : (encode message).length ≤ 12306 := by
  have bound_mmParameterGrpComp := message.mmParameterGrpComp.length_lt
  unfold encode
  simp only [List.length_append, Alpha.encode_length, NrResponseHeaderMeComp.encode_length, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const MmParameterGrpComp.encode 48 MmParameterGrpComp.encode_length]
  omega

@[simp] theorem decode_encode (message : InquireMmParameterResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [NrResponseHeaderMeComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 MmParameterGrpComp.encode MmParameterGrpComp.decode MmParameterGrpComp.decode_encode]
  simp only [Option.bind_some]
  simp only [message.mmParameterGrpComp.length_lt, ↓reduceDIte]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : InquireMmParameterResponse) : decode (encode message) = some (message, []) := by
  have trailing := decode_encode message []
  rw [List.append_nil] at trailing
  exact trailing

end InquireMmParameterResponse

/-- Inquire Margin Based Risk Limit Response: 66 bytes -/
structure InquireMarginBasedRiskLimitResponse where
  pad2 : Alpha 2
  nrResponseHeaderMeComp : NrResponseHeaderMeComp
  marginBasedRiskLimitLong : BitVec 64
  marginBasedRiskLimitShort : BitVec 64
  deriving DecidableEq, Repr

namespace InquireMarginBasedRiskLimitResponse

def encode (message : InquireMarginBasedRiskLimitResponse) : List UInt8 :=
  Alpha.encode message.pad2
    ++ NrResponseHeaderMeComp.encode message.nrResponseHeaderMeComp
    ++ encodeUIntLE 8 message.marginBasedRiskLimitLong
    ++ encodeUIntLE 8 message.marginBasedRiskLimitShort

def decode (bytes : List UInt8) : Option (InquireMarginBasedRiskLimitResponse × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (nrResponseHeaderMeComp, bytes) ← NrResponseHeaderMeComp.decode bytes
  let (marginBasedRiskLimitLong, bytes) ← decodeUIntLE 8 bytes
  let (marginBasedRiskLimitShort, bytes) ← decodeUIntLE 8 bytes
  pure ({ pad2, nrResponseHeaderMeComp, marginBasedRiskLimitLong, marginBasedRiskLimitShort }, bytes)

@[simp] theorem encode_length (message : InquireMarginBasedRiskLimitResponse) : (encode message).length = 66 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, NrResponseHeaderMeComp.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : InquireMarginBasedRiskLimitResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InquireMarginBasedRiskLimitResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [NrResponseHeaderMeComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : InquireMarginBasedRiskLimitResponse) : decode (encode message) = some (message, []) := by
  have trailing := decode_encode message []
  rw [List.append_nil] at trailing
  exact trailing

end InquireMarginBasedRiskLimitResponse

/-- Sessions Grp Comp: 40 bytes -/
structure SessionsGrpComp where
  partyIdSessionId : BitVec 32
  partyIdSponsoredAccessUnit : BitVec 32
  sessionMode : BitVec 8
  sessionSubMode : BitVec 8
  partySponsoredAccessUnit : Alpha 30
  deriving DecidableEq, Repr

namespace SessionsGrpComp

def encode (message : SessionsGrpComp) : List UInt8 :=
  encodeUIntLE 4 message.partyIdSessionId
    ++ encodeUIntLE 4 message.partyIdSponsoredAccessUnit
    ++ encodeUInt 1 message.sessionMode
    ++ encodeUInt 1 message.sessionSubMode
    ++ Alpha.encode message.partySponsoredAccessUnit

def decode (bytes : List UInt8) : Option (SessionsGrpComp × List UInt8) := do
  let (partyIdSessionId, bytes) ← decodeUIntLE 4 bytes
  let (partyIdSponsoredAccessUnit, bytes) ← decodeUIntLE 4 bytes
  let (sessionMode, bytes) ← decodeUInt 1 bytes
  let (sessionSubMode, bytes) ← decodeUInt 1 bytes
  let (partySponsoredAccessUnit, bytes) ← Alpha.decode 30 bytes
  pure ({ partyIdSessionId, partyIdSponsoredAccessUnit, sessionMode, sessionSubMode, partySponsoredAccessUnit }, bytes)

@[simp] theorem encode_length (message : SessionsGrpComp) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : SessionsGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SessionsGrpComp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end SessionsGrpComp

/-- Inquire Session List Response -/
structure InquireSessionListResponse where
  pad2 : Alpha 2
  responseHeaderComp : ResponseHeaderComp
  pad6 : Alpha 6
  sessionsGrpComp : Bounded 2 SessionsGrpComp
  deriving DecidableEq, Repr

namespace InquireSessionListResponse

def encode (message : InquireSessionListResponse) : List UInt8 :=
  Alpha.encode message.pad2
    ++ ResponseHeaderComp.encode message.responseHeaderComp
    ++ encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.sessionsGrpComp.val.length)
    ++ Alpha.encode message.pad6
    ++ encodeMany SessionsGrpComp.encode message.sessionsGrpComp.val

def decode (bytes : List UInt8) : Option (InquireSessionListResponse × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (responseHeaderComp, bytes) ← ResponseHeaderComp.decode bytes
  let (noSessions, bytes) ← decodeUIntLE 2 bytes
  let (pad6, bytes) ← Alpha.decode 6 bytes
  let (sessionsGrpComp_, bytes) ← decodeMany SessionsGrpComp.decode noSessions.toNat bytes
  if fits_sessionsGrpComp : sessionsGrpComp_.length < 256 ^ 2 then
    pure ({ pad2, responseHeaderComp, pad6, sessionsGrpComp := ⟨sessionsGrpComp_, fits_sessionsGrpComp⟩ }, bytes)
  else none

theorem encode_length_pos (message : InquireSessionListResponse) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : InquireSessionListResponse) : (encode message).length ≤ 2621434 := by
  have bound_sessionsGrpComp := message.sessionsGrpComp.length_lt
  unfold encode
  simp only [List.length_append, Alpha.encode_length, ResponseHeaderComp.encode_length, encodeUIntLE_length, encodeMany_length_const SessionsGrpComp.encode 40 SessionsGrpComp.encode_length]
  omega

@[simp] theorem decode_encode (message : InquireSessionListResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [ResponseHeaderComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 2 SessionsGrpComp.encode SessionsGrpComp.decode SessionsGrpComp.decode_encode]
  simp only [Option.bind_some]
  simp only [message.sessionsGrpComp.length_lt, ↓reduceDIte]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : InquireSessionListResponse) : decode (encode message) = some (message, []) := by
  have trailing := decode_encode message []
  rw [List.append_nil] at trailing
  exact trailing

end InquireSessionListResponse

/-- Party Details Grp Comp: 56 bytes -/
structure PartyDetailsGrpComp where
  partyDetailIdExecutingTrader : BitVec 32
  partyIdSponsoredAccessUnit : BitVec 32
  partyDetailExecutingTrader : Alpha 6
  partyDetailRoleQualifier : BitVec 8
  partyDetailStatus : BitVec 8
  partyDetailDeskId : Alpha 3
  partySponsoredAccessUnit : Alpha 30
  pad7 : Alpha 7
  deriving DecidableEq, Repr

namespace PartyDetailsGrpComp

def encode (message : PartyDetailsGrpComp) : List UInt8 :=
  encodeUIntLE 4 message.partyDetailIdExecutingTrader
    ++ encodeUIntLE 4 message.partyIdSponsoredAccessUnit
    ++ Alpha.encode message.partyDetailExecutingTrader
    ++ encodeUInt 1 message.partyDetailRoleQualifier
    ++ encodeUInt 1 message.partyDetailStatus
    ++ Alpha.encode message.partyDetailDeskId
    ++ Alpha.encode message.partySponsoredAccessUnit
    ++ Alpha.encode message.pad7

def decode (bytes : List UInt8) : Option (PartyDetailsGrpComp × List UInt8) := do
  let (partyDetailIdExecutingTrader, bytes) ← decodeUIntLE 4 bytes
  let (partyIdSponsoredAccessUnit, bytes) ← decodeUIntLE 4 bytes
  let (partyDetailExecutingTrader, bytes) ← Alpha.decode 6 bytes
  let (partyDetailRoleQualifier, bytes) ← decodeUInt 1 bytes
  let (partyDetailStatus, bytes) ← decodeUInt 1 bytes
  let (partyDetailDeskId, bytes) ← Alpha.decode 3 bytes
  let (partySponsoredAccessUnit, bytes) ← Alpha.decode 30 bytes
  let (pad7, bytes) ← Alpha.decode 7 bytes
  pure ({ partyDetailIdExecutingTrader, partyIdSponsoredAccessUnit, partyDetailExecutingTrader, partyDetailRoleQualifier, partyDetailStatus, partyDetailDeskId, partySponsoredAccessUnit, pad7 }, bytes)

@[simp] theorem encode_length (message : PartyDetailsGrpComp) : (encode message).length = 56 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : PartyDetailsGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PartyDetailsGrpComp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end PartyDetailsGrpComp

/-- Inquire User Response -/
structure InquireUserResponse where
  pad2 : Alpha 2
  responseHeaderComp : ResponseHeaderComp
  lastEntityProcessed : Alpha 16
  pad6 : Alpha 6
  partyDetailsGrpComp : Bounded 2 PartyDetailsGrpComp
  deriving DecidableEq, Repr

namespace InquireUserResponse

def encode (message : InquireUserResponse) : List UInt8 :=
  Alpha.encode message.pad2
    ++ ResponseHeaderComp.encode message.responseHeaderComp
    ++ Alpha.encode message.lastEntityProcessed
    ++ encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.partyDetailsGrpComp.val.length)
    ++ Alpha.encode message.pad6
    ++ encodeMany PartyDetailsGrpComp.encode message.partyDetailsGrpComp.val

def decode (bytes : List UInt8) : Option (InquireUserResponse × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (responseHeaderComp, bytes) ← ResponseHeaderComp.decode bytes
  let (lastEntityProcessed, bytes) ← Alpha.decode 16 bytes
  let (noPartyDetails, bytes) ← decodeUIntLE 2 bytes
  let (pad6, bytes) ← Alpha.decode 6 bytes
  let (partyDetailsGrpComp_, bytes) ← decodeMany PartyDetailsGrpComp.decode noPartyDetails.toNat bytes
  if fits_partyDetailsGrpComp : partyDetailsGrpComp_.length < 256 ^ 2 then
    pure ({ pad2, responseHeaderComp, lastEntityProcessed, pad6, partyDetailsGrpComp := ⟨partyDetailsGrpComp_, fits_partyDetailsGrpComp⟩ }, bytes)
  else none

theorem encode_length_pos (message : InquireUserResponse) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : InquireUserResponse) : (encode message).length ≤ 3670010 := by
  have bound_partyDetailsGrpComp := message.partyDetailsGrpComp.length_lt
  unfold encode
  simp only [List.length_append, Alpha.encode_length, ResponseHeaderComp.encode_length, encodeUIntLE_length, encodeMany_length_const PartyDetailsGrpComp.encode 56 PartyDetailsGrpComp.encode_length]
  omega

@[simp] theorem decode_encode (message : InquireUserResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [ResponseHeaderComp.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 2 PartyDetailsGrpComp.encode PartyDetailsGrpComp.decode PartyDetailsGrpComp.decode_encode]
  simp only [Option.bind_some]
  simp only [message.partyDetailsGrpComp.length_lt, ↓reduceDIte]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : InquireUserResponse) : decode (encode message) = some (message, []) := by
  have trailing := decode_encode message []
  rw [List.append_nil] at trailing
  exact trailing

end InquireUserResponse

/-- Legal Notification Broadcast -/
structure LegalNotificationBroadcast where
  pad2 : Alpha 2
  rbcHeaderComp : RbcHeaderComp
  transactTime : BitVec 64
  userStatus : BitVec 8
  varText : Bounded 2 UInt8
  alignmentPadding : Capped 4282374239
  deriving DecidableEq, Repr

namespace LegalNotificationBroadcast

def encode (message : LegalNotificationBroadcast) : List UInt8 :=
  Alpha.encode message.pad2
    ++ RbcHeaderComp.encode message.rbcHeaderComp
    ++ encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.varText.val.length)
    ++ encodeUInt 1 message.userStatus
    ++ encodeMany Byte.encode message.varText.val
    ++ message.alignmentPadding.val

def decode (bytes : List UInt8) : Option LegalNotificationBroadcast := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderComp, bytes) ← RbcHeaderComp.decode bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (varTextLen, bytes) ← decodeUIntLE 2 bytes
  let (userStatus, bytes) ← decodeUInt 1 bytes
  let (varText_, bytes) ← decodeMany Byte.decode varTextLen.toNat bytes
  let alignmentPadding_ := bytes
  if fits_varText : varText_.length < 256 ^ 2 then
    if fits_alignmentPadding : alignmentPadding_.length ≤ 4282374239 then
      pure { pad2, rbcHeaderComp, transactTime, userStatus, varText := ⟨varText_, fits_varText⟩, alignmentPadding := ⟨alignmentPadding_, fits_alignmentPadding⟩ }
    else none
  else none

theorem encode_length_pos (message : LegalNotificationBroadcast) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : LegalNotificationBroadcast) : (encode message).length ≤ 4282439819 := by
  have bound_varText := message.varText.length_lt
  have bound_alignmentPadding := message.alignmentPadding.length_le
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RbcHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const Byte.encode 1 Byte.encode_length]
  omega

theorem decode_encode (message : LegalNotificationBroadcast) : decode (encode message) = some message := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [RbcHeaderComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 2 Byte.encode Byte.decode Byte.decode_encode]
  simp only [Option.bind_some]
  simp only [message.varText.length_lt, message.alignmentPadding.length_le, ↓reduceDIte]
  rfl

end LegalNotificationBroadcast

/-- Logon Response -/
structure LogonResponse where
  pad2 : Alpha 2
  responseHeaderComp : ResponseHeaderComp
  throttleTimeInterval : BitVec 64
  throttleNoMsgs : BitVec 32
  throttleDisconnectLimit : BitVec 32
  heartBtInt : BitVec 32
  sessionInstanceId : BitVec 32
  latestPublicKeySeqNo : BitVec 32
  marketId : BitVec 16
  tradSesMode : BitVec 8
  defaultCstmApplVerId : Alpha 30
  defaultCstmApplVerSubId : Alpha 5
  partitionId : BitVec 16
  publicKey : Bounded 2 UInt8
  alignmentPadding : Capped 4282374239
  deriving DecidableEq, Repr

namespace LogonResponse

def encode (message : LogonResponse) : List UInt8 :=
  Alpha.encode message.pad2
    ++ ResponseHeaderComp.encode message.responseHeaderComp
    ++ encodeUIntLE 8 message.throttleTimeInterval
    ++ encodeUIntLE 4 message.throttleNoMsgs
    ++ encodeUIntLE 4 message.throttleDisconnectLimit
    ++ encodeUIntLE 4 message.heartBtInt
    ++ encodeUIntLE 4 message.sessionInstanceId
    ++ encodeUIntLE 4 message.latestPublicKeySeqNo
    ++ encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.publicKey.val.length)
    ++ encodeUIntLE 2 message.marketId
    ++ encodeUInt 1 message.tradSesMode
    ++ Alpha.encode message.defaultCstmApplVerId
    ++ Alpha.encode message.defaultCstmApplVerSubId
    ++ encodeUIntLE 2 message.partitionId
    ++ encodeMany Byte.encode message.publicKey.val
    ++ message.alignmentPadding.val

def decode (bytes : List UInt8) : Option LogonResponse := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (responseHeaderComp, bytes) ← ResponseHeaderComp.decode bytes
  let (throttleTimeInterval, bytes) ← decodeUIntLE 8 bytes
  let (throttleNoMsgs, bytes) ← decodeUIntLE 4 bytes
  let (throttleDisconnectLimit, bytes) ← decodeUIntLE 4 bytes
  let (heartBtInt, bytes) ← decodeUIntLE 4 bytes
  let (sessionInstanceId, bytes) ← decodeUIntLE 4 bytes
  let (latestPublicKeySeqNo, bytes) ← decodeUIntLE 4 bytes
  let (publicKeyLen, bytes) ← decodeUIntLE 2 bytes
  let (marketId, bytes) ← decodeUIntLE 2 bytes
  let (tradSesMode, bytes) ← decodeUInt 1 bytes
  let (defaultCstmApplVerId, bytes) ← Alpha.decode 30 bytes
  let (defaultCstmApplVerSubId, bytes) ← Alpha.decode 5 bytes
  let (partitionId, bytes) ← decodeUIntLE 2 bytes
  let (publicKey_, bytes) ← decodeMany Byte.decode publicKeyLen.toNat bytes
  let alignmentPadding_ := bytes
  if fits_publicKey : publicKey_.length < 256 ^ 2 then
    if fits_alignmentPadding : alignmentPadding_.length ≤ 4282374239 then
      pure { pad2, responseHeaderComp, throttleTimeInterval, throttleNoMsgs, throttleDisconnectLimit, heartBtInt, sessionInstanceId, latestPublicKeySeqNo, marketId, tradSesMode, defaultCstmApplVerId, defaultCstmApplVerSubId, partitionId, publicKey := ⟨publicKey_, fits_publicKey⟩, alignmentPadding := ⟨alignmentPadding_, fits_alignmentPadding⟩ }
    else none
  else none

theorem encode_length_pos (message : LogonResponse) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : LogonResponse) : (encode message).length ≤ 4282439870 := by
  have bound_publicKey := message.publicKey.length_lt
  have bound_alignmentPadding := message.alignmentPadding.length_le
  unfold encode
  simp only [List.length_append, Alpha.encode_length, ResponseHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const Byte.encode 1 Byte.encode_length]
  omega

theorem decode_encode (message : LogonResponse) : decode (encode message) = some message := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [ResponseHeaderComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 2 Byte.encode Byte.decode Byte.decode_encode]
  simp only [Option.bind_some]
  simp only [message.publicKey.length_lt, message.alignmentPadding.length_le, ↓reduceDIte]
  rfl

end LogonResponse

/-- Logout Response: 26 bytes -/
structure LogoutResponse where
  pad2 : Alpha 2
  responseHeaderComp : ResponseHeaderComp
  deriving DecidableEq, Repr

namespace LogoutResponse

def encode (message : LogoutResponse) : List UInt8 :=
  Alpha.encode message.pad2
    ++ ResponseHeaderComp.encode message.responseHeaderComp

def decode (bytes : List UInt8) : Option (LogoutResponse × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (responseHeaderComp, bytes) ← ResponseHeaderComp.decode bytes
  pure ({ pad2, responseHeaderComp }, bytes)

@[simp] theorem encode_length (message : LogoutResponse) : (encode message).length = 26 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, ResponseHeaderComp.encode_length]

theorem encode_length_pos (message : LogoutResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LogoutResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [ResponseHeaderComp.decode_encode, Option.bind_some]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : LogoutResponse) : decode (encode message) = some (message, []) := by
  have trailing := decode_encode message []
  rw [List.append_nil] at trailing
  exact trailing

end LogoutResponse

/-- Mm Parameter Definition Response: 58 bytes -/
structure MmParameterDefinitionResponse where
  pad2 : Alpha 2
  nrResponseHeaderMeComp : NrResponseHeaderMeComp
  execId : BitVec 64
  deriving DecidableEq, Repr

namespace MmParameterDefinitionResponse

def encode (message : MmParameterDefinitionResponse) : List UInt8 :=
  Alpha.encode message.pad2
    ++ NrResponseHeaderMeComp.encode message.nrResponseHeaderMeComp
    ++ encodeUIntLE 8 message.execId

def decode (bytes : List UInt8) : Option (MmParameterDefinitionResponse × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (nrResponseHeaderMeComp, bytes) ← NrResponseHeaderMeComp.decode bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  pure ({ pad2, nrResponseHeaderMeComp, execId }, bytes)

@[simp] theorem encode_length (message : MmParameterDefinitionResponse) : (encode message).length = 58 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, NrResponseHeaderMeComp.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : MmParameterDefinitionResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MmParameterDefinitionResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [NrResponseHeaderMeComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : MmParameterDefinitionResponse) : decode (encode message) = some (message, []) := by
  have trailing := decode_encode message []
  rw [List.append_nil] at trailing
  exact trailing

end MmParameterDefinitionResponse

/-- Mass Order Ack: 66 bytes -/
structure MassOrderAck where
  pad2 : Alpha 2
  nrResponseHeaderMeComp : NrResponseHeaderMeComp
  massOrderRequestId : BitVec 64
  massOrderReportId : BitVec 32
  pad4 : Alpha 4
  deriving DecidableEq, Repr

namespace MassOrderAck

def encode (message : MassOrderAck) : List UInt8 :=
  Alpha.encode message.pad2
    ++ NrResponseHeaderMeComp.encode message.nrResponseHeaderMeComp
    ++ encodeUIntLE 8 message.massOrderRequestId
    ++ encodeUIntLE 4 message.massOrderReportId
    ++ Alpha.encode message.pad4

def decode (bytes : List UInt8) : Option (MassOrderAck × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (nrResponseHeaderMeComp, bytes) ← NrResponseHeaderMeComp.decode bytes
  let (massOrderRequestId, bytes) ← decodeUIntLE 8 bytes
  let (massOrderReportId, bytes) ← decodeUIntLE 4 bytes
  let (pad4, bytes) ← Alpha.decode 4 bytes
  pure ({ pad2, nrResponseHeaderMeComp, massOrderRequestId, massOrderReportId, pad4 }, bytes)

@[simp] theorem encode_length (message : MassOrderAck) : (encode message).length = 66 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, NrResponseHeaderMeComp.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : MassOrderAck) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MassOrderAck) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [NrResponseHeaderMeComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : MassOrderAck) : decode (encode message) = some (message, []) := by
  have trailing := decode_encode message []
  rw [List.append_nil] at trailing
  exact trailing

end MassOrderAck

/-- Quote Entry Ack Grp Comp: 24 bytes -/
structure QuoteEntryAckGrpComp where
  securityId : BitVec 64
  cxlSize : BitVec 64
  quoteEntryRejectReason : BitVec 32
  quoteEntryStatus : BitVec 8
  side : BitVec 8
  pad2 : Alpha 2
  deriving DecidableEq, Repr

namespace QuoteEntryAckGrpComp

def encode (message : QuoteEntryAckGrpComp) : List UInt8 :=
  encodeUIntLE 8 message.securityId
    ++ encodeUIntLE 8 message.cxlSize
    ++ encodeUIntLE 4 message.quoteEntryRejectReason
    ++ encodeUInt 1 message.quoteEntryStatus
    ++ encodeUInt 1 message.side
    ++ Alpha.encode message.pad2

def decode (bytes : List UInt8) : Option (QuoteEntryAckGrpComp × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (cxlSize, bytes) ← decodeUIntLE 8 bytes
  let (quoteEntryRejectReason, bytes) ← decodeUIntLE 4 bytes
  let (quoteEntryStatus, bytes) ← decodeUInt 1 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  pure ({ securityId, cxlSize, quoteEntryRejectReason, quoteEntryStatus, side, pad2 }, bytes)

@[simp] theorem encode_length (message : QuoteEntryAckGrpComp) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : QuoteEntryAckGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : QuoteEntryAckGrpComp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end QuoteEntryAckGrpComp

/-- Mass Quote Response -/
structure MassQuoteResponse where
  pad2 : Alpha 2
  nrResponseHeaderMeComp : NrResponseHeaderMeComp
  quoteId : BitVec 64
  quoteResponseId : BitVec 64
  marketSegmentId : BitVec 32
  pad3 : Alpha 3
  quoteEntryAckGrpComp : Bounded 1 QuoteEntryAckGrpComp
  deriving DecidableEq, Repr

namespace MassQuoteResponse

def encode (message : MassQuoteResponse) : List UInt8 :=
  Alpha.encode message.pad2
    ++ NrResponseHeaderMeComp.encode message.nrResponseHeaderMeComp
    ++ encodeUIntLE 8 message.quoteId
    ++ encodeUIntLE 8 message.quoteResponseId
    ++ encodeUIntLE 4 message.marketSegmentId
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.quoteEntryAckGrpComp.val.length)
    ++ Alpha.encode message.pad3
    ++ encodeMany QuoteEntryAckGrpComp.encode message.quoteEntryAckGrpComp.val

def decode (bytes : List UInt8) : Option (MassQuoteResponse × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (nrResponseHeaderMeComp, bytes) ← NrResponseHeaderMeComp.decode bytes
  let (quoteId, bytes) ← decodeUIntLE 8 bytes
  let (quoteResponseId, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (noQuoteSideEntries, bytes) ← decodeUInt 1 bytes
  let (pad3, bytes) ← Alpha.decode 3 bytes
  let (quoteEntryAckGrpComp_, bytes) ← decodeMany QuoteEntryAckGrpComp.decode noQuoteSideEntries.toNat bytes
  if fits_quoteEntryAckGrpComp : quoteEntryAckGrpComp_.length < 256 ^ 1 then
    pure ({ pad2, nrResponseHeaderMeComp, quoteId, quoteResponseId, marketSegmentId, pad3, quoteEntryAckGrpComp := ⟨quoteEntryAckGrpComp_, fits_quoteEntryAckGrpComp⟩ }, bytes)
  else none

theorem encode_length_pos (message : MassQuoteResponse) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MassQuoteResponse) : (encode message).length ≤ 6194 := by
  have bound_quoteEntryAckGrpComp := message.quoteEntryAckGrpComp.length_lt
  unfold encode
  simp only [List.length_append, Alpha.encode_length, NrResponseHeaderMeComp.encode_length, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const QuoteEntryAckGrpComp.encode 24 QuoteEntryAckGrpComp.encode_length]
  omega

@[simp] theorem decode_encode (message : MassQuoteResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [NrResponseHeaderMeComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 QuoteEntryAckGrpComp.encode QuoteEntryAckGrpComp.decode QuoteEntryAckGrpComp.decode_encode]
  simp only [Option.bind_some]
  simp only [message.quoteEntryAckGrpComp.length_lt, ↓reduceDIte]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : MassQuoteResponse) : decode (encode message) = some (message, []) := by
  have trailing := decode_encode message []
  rw [List.append_nil] at trailing
  exact trailing

end MassQuoteResponse

/-- Order Event Grp Comp: 24 bytes -/
structure OrderEventGrpComp where
  orderEventPx : BitVec 64
  orderEventQty : BitVec 64
  orderEventMatchId : BitVec 32
  orderEventReason : BitVec 8
  pad3 : Alpha 3
  deriving DecidableEq, Repr

namespace OrderEventGrpComp

def encode (message : OrderEventGrpComp) : List UInt8 :=
  encodeUIntLE 8 message.orderEventPx
    ++ encodeUIntLE 8 message.orderEventQty
    ++ encodeUIntLE 4 message.orderEventMatchId
    ++ encodeUInt 1 message.orderEventReason
    ++ Alpha.encode message.pad3

def decode (bytes : List UInt8) : Option (OrderEventGrpComp × List UInt8) := do
  let (orderEventPx, bytes) ← decodeUIntLE 8 bytes
  let (orderEventQty, bytes) ← decodeUIntLE 8 bytes
  let (orderEventMatchId, bytes) ← decodeUIntLE 4 bytes
  let (orderEventReason, bytes) ← decodeUInt 1 bytes
  let (pad3, bytes) ← Alpha.decode 3 bytes
  pure ({ orderEventPx, orderEventQty, orderEventMatchId, orderEventReason, pad3 }, bytes)

@[simp] theorem encode_length (message : OrderEventGrpComp) : (encode message).length = 24 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : OrderEventGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderEventGrpComp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end OrderEventGrpComp

/-- Modify Order Nr Response -/
structure ModifyOrderNrResponse where
  pad2 : Alpha 2
  nrResponseHeaderMeComp : NrResponseHeaderMeComp
  orderId : BitVec 64
  clOrdId : BitVec 64
  origClOrdId : BitVec 64
  securityId : BitVec 64
  execId : BitVec 64
  leavesQty : BitVec 64
  cumQty : BitVec 64
  cxlQty : BitVec 64
  ordStatus : OrdStatus
  execType : ExecType
  execRestatementReason : BitVec 16
  crossedIndicator : BitVec 8
  productComplex : BitVec 8
  triggered : BitVec 8
  transactionDelayIndicator : BitVec 8
  pad7 : Alpha 7
  orderEventGrpComp : Bounded 1 OrderEventGrpComp
  deriving DecidableEq, Repr

namespace ModifyOrderNrResponse

def encode (message : ModifyOrderNrResponse) : List UInt8 :=
  Alpha.encode message.pad2
    ++ NrResponseHeaderMeComp.encode message.nrResponseHeaderMeComp
    ++ encodeUIntLE 8 message.orderId
    ++ encodeUIntLE 8 message.clOrdId
    ++ encodeUIntLE 8 message.origClOrdId
    ++ encodeUIntLE 8 message.securityId
    ++ encodeUIntLE 8 message.execId
    ++ encodeUIntLE 8 message.leavesQty
    ++ encodeUIntLE 8 message.cumQty
    ++ encodeUIntLE 8 message.cxlQty
    ++ OrdStatus.encode message.ordStatus
    ++ ExecType.encode message.execType
    ++ encodeUIntLE 2 message.execRestatementReason
    ++ encodeUInt 1 message.crossedIndicator
    ++ encodeUInt 1 message.productComplex
    ++ encodeUInt 1 message.triggered
    ++ encodeUInt 1 message.transactionDelayIndicator
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.orderEventGrpComp.val.length)
    ++ Alpha.encode message.pad7
    ++ encodeMany OrderEventGrpComp.encode message.orderEventGrpComp.val

def decode (bytes : List UInt8) : Option (ModifyOrderNrResponse × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (nrResponseHeaderMeComp, bytes) ← NrResponseHeaderMeComp.decode bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (origClOrdId, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  let (leavesQty, bytes) ← decodeUIntLE 8 bytes
  let (cumQty, bytes) ← decodeUIntLE 8 bytes
  let (cxlQty, bytes) ← decodeUIntLE 8 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (execRestatementReason, bytes) ← decodeUIntLE 2 bytes
  let (crossedIndicator, bytes) ← decodeUInt 1 bytes
  let (productComplex, bytes) ← decodeUInt 1 bytes
  let (triggered, bytes) ← decodeUInt 1 bytes
  let (transactionDelayIndicator, bytes) ← decodeUInt 1 bytes
  let (noOrderEvents, bytes) ← decodeUInt 1 bytes
  let (pad7, bytes) ← Alpha.decode 7 bytes
  let (orderEventGrpComp_, bytes) ← decodeMany OrderEventGrpComp.decode noOrderEvents.toNat bytes
  if fits_orderEventGrpComp : orderEventGrpComp_.length < 256 ^ 1 then
    pure ({ pad2, nrResponseHeaderMeComp, orderId, clOrdId, origClOrdId, securityId, execId, leavesQty, cumQty, cxlQty, ordStatus, execType, execRestatementReason, crossedIndicator, productComplex, triggered, transactionDelayIndicator, pad7, orderEventGrpComp := ⟨orderEventGrpComp_, fits_orderEventGrpComp⟩ }, bytes)
  else none

theorem encode_length_pos (message : ModifyOrderNrResponse) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ModifyOrderNrResponse) : (encode message).length ≤ 6250 := by
  have bound_orderEventGrpComp := message.orderEventGrpComp.length_lt
  unfold encode
  simp only [List.length_append, Alpha.encode_length, NrResponseHeaderMeComp.encode_length, encodeUIntLE_length, OrdStatus.encode_length, ExecType.encode_length, encodeUInt_length, encodeMany_length_const OrderEventGrpComp.encode 24 OrderEventGrpComp.encode_length]
  omega

@[simp] theorem decode_encode (message : ModifyOrderNrResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [NrResponseHeaderMeComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [OrdStatus.decode_encode]
  simp only [Option.bind_some]
  rw [ExecType.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 OrderEventGrpComp.encode OrderEventGrpComp.decode OrderEventGrpComp.decode_encode]
  simp only [Option.bind_some]
  simp only [message.orderEventGrpComp.length_lt, ↓reduceDIte]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : ModifyOrderNrResponse) : decode (encode message) = some (message, []) := by
  have trailing := decode_encode message []
  rw [List.append_nil] at trailing
  exact trailing

end ModifyOrderNrResponse

/-- Modify Order Response -/
structure ModifyOrderResponse where
  pad2 : Alpha 2
  responseHeaderMeComp : ResponseHeaderMeComp
  orderId : BitVec 64
  clOrdId : BitVec 64
  origClOrdId : BitVec 64
  securityId : BitVec 64
  execId : BitVec 64
  leavesQty : BitVec 64
  cumQty : BitVec 64
  cxlQty : BitVec 64
  trdRegTsTimePriority : BitVec 64
  ordStatus : OrdStatus
  execType : ExecType
  execRestatementReason : BitVec 16
  crossedIndicator : BitVec 8
  productComplex : BitVec 8
  triggered : BitVec 8
  transactionDelayIndicator : BitVec 8
  pad7 : Alpha 7
  orderEventGrpComp : Bounded 1 OrderEventGrpComp
  deriving DecidableEq, Repr

namespace ModifyOrderResponse

def encode (message : ModifyOrderResponse) : List UInt8 :=
  Alpha.encode message.pad2
    ++ ResponseHeaderMeComp.encode message.responseHeaderMeComp
    ++ encodeUIntLE 8 message.orderId
    ++ encodeUIntLE 8 message.clOrdId
    ++ encodeUIntLE 8 message.origClOrdId
    ++ encodeUIntLE 8 message.securityId
    ++ encodeUIntLE 8 message.execId
    ++ encodeUIntLE 8 message.leavesQty
    ++ encodeUIntLE 8 message.cumQty
    ++ encodeUIntLE 8 message.cxlQty
    ++ encodeUIntLE 8 message.trdRegTsTimePriority
    ++ OrdStatus.encode message.ordStatus
    ++ ExecType.encode message.execType
    ++ encodeUIntLE 2 message.execRestatementReason
    ++ encodeUInt 1 message.crossedIndicator
    ++ encodeUInt 1 message.productComplex
    ++ encodeUInt 1 message.triggered
    ++ encodeUInt 1 message.transactionDelayIndicator
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.orderEventGrpComp.val.length)
    ++ Alpha.encode message.pad7
    ++ encodeMany OrderEventGrpComp.encode message.orderEventGrpComp.val

def decode (bytes : List UInt8) : Option (ModifyOrderResponse × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (responseHeaderMeComp, bytes) ← ResponseHeaderMeComp.decode bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (origClOrdId, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  let (leavesQty, bytes) ← decodeUIntLE 8 bytes
  let (cumQty, bytes) ← decodeUIntLE 8 bytes
  let (cxlQty, bytes) ← decodeUIntLE 8 bytes
  let (trdRegTsTimePriority, bytes) ← decodeUIntLE 8 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (execRestatementReason, bytes) ← decodeUIntLE 2 bytes
  let (crossedIndicator, bytes) ← decodeUInt 1 bytes
  let (productComplex, bytes) ← decodeUInt 1 bytes
  let (triggered, bytes) ← decodeUInt 1 bytes
  let (transactionDelayIndicator, bytes) ← decodeUInt 1 bytes
  let (noOrderEvents, bytes) ← decodeUInt 1 bytes
  let (pad7, bytes) ← Alpha.decode 7 bytes
  let (orderEventGrpComp_, bytes) ← decodeMany OrderEventGrpComp.decode noOrderEvents.toNat bytes
  if fits_orderEventGrpComp : orderEventGrpComp_.length < 256 ^ 1 then
    pure ({ pad2, responseHeaderMeComp, orderId, clOrdId, origClOrdId, securityId, execId, leavesQty, cumQty, cxlQty, trdRegTsTimePriority, ordStatus, execType, execRestatementReason, crossedIndicator, productComplex, triggered, transactionDelayIndicator, pad7, orderEventGrpComp := ⟨orderEventGrpComp_, fits_orderEventGrpComp⟩ }, bytes)
  else none

theorem encode_length_pos (message : ModifyOrderResponse) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ModifyOrderResponse) : (encode message).length ≤ 6274 := by
  have bound_orderEventGrpComp := message.orderEventGrpComp.length_lt
  unfold encode
  simp only [List.length_append, Alpha.encode_length, ResponseHeaderMeComp.encode_length, encodeUIntLE_length, OrdStatus.encode_length, ExecType.encode_length, encodeUInt_length, encodeMany_length_const OrderEventGrpComp.encode 24 OrderEventGrpComp.encode_length]
  omega

@[simp] theorem decode_encode (message : ModifyOrderResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [ResponseHeaderMeComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [OrdStatus.decode_encode]
  simp only [Option.bind_some]
  rw [ExecType.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 OrderEventGrpComp.encode OrderEventGrpComp.decode OrderEventGrpComp.decode_encode]
  simp only [Option.bind_some]
  simp only [message.orderEventGrpComp.length_lt, ↓reduceDIte]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : ModifyOrderResponse) : decode (encode message) = some (message, []) := by
  have trailing := decode_encode message []
  rw [List.append_nil] at trailing
  exact trailing

end ModifyOrderResponse

/-- New Order Nr Response -/
structure NewOrderNrResponse where
  pad2 : Alpha 2
  nrResponseHeaderMeComp : NrResponseHeaderMeComp
  orderId : BitVec 64
  clOrdId : BitVec 64
  securityId : BitVec 64
  execId : BitVec 64
  leavesQty : BitVec 64
  cxlQty : BitVec 64
  ordStatus : OrdStatus
  execType : ExecType
  execRestatementReason : BitVec 16
  crossedIndicator : BitVec 8
  productComplex : BitVec 8
  triggered : BitVec 8
  transactionDelayIndicator : BitVec 8
  pad7 : Alpha 7
  orderEventGrpComp : Bounded 1 OrderEventGrpComp
  deriving DecidableEq, Repr

namespace NewOrderNrResponse

def encode (message : NewOrderNrResponse) : List UInt8 :=
  Alpha.encode message.pad2
    ++ NrResponseHeaderMeComp.encode message.nrResponseHeaderMeComp
    ++ encodeUIntLE 8 message.orderId
    ++ encodeUIntLE 8 message.clOrdId
    ++ encodeUIntLE 8 message.securityId
    ++ encodeUIntLE 8 message.execId
    ++ encodeUIntLE 8 message.leavesQty
    ++ encodeUIntLE 8 message.cxlQty
    ++ OrdStatus.encode message.ordStatus
    ++ ExecType.encode message.execType
    ++ encodeUIntLE 2 message.execRestatementReason
    ++ encodeUInt 1 message.crossedIndicator
    ++ encodeUInt 1 message.productComplex
    ++ encodeUInt 1 message.triggered
    ++ encodeUInt 1 message.transactionDelayIndicator
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.orderEventGrpComp.val.length)
    ++ Alpha.encode message.pad7
    ++ encodeMany OrderEventGrpComp.encode message.orderEventGrpComp.val

def decode (bytes : List UInt8) : Option (NewOrderNrResponse × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (nrResponseHeaderMeComp, bytes) ← NrResponseHeaderMeComp.decode bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  let (leavesQty, bytes) ← decodeUIntLE 8 bytes
  let (cxlQty, bytes) ← decodeUIntLE 8 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (execRestatementReason, bytes) ← decodeUIntLE 2 bytes
  let (crossedIndicator, bytes) ← decodeUInt 1 bytes
  let (productComplex, bytes) ← decodeUInt 1 bytes
  let (triggered, bytes) ← decodeUInt 1 bytes
  let (transactionDelayIndicator, bytes) ← decodeUInt 1 bytes
  let (noOrderEvents, bytes) ← decodeUInt 1 bytes
  let (pad7, bytes) ← Alpha.decode 7 bytes
  let (orderEventGrpComp_, bytes) ← decodeMany OrderEventGrpComp.decode noOrderEvents.toNat bytes
  if fits_orderEventGrpComp : orderEventGrpComp_.length < 256 ^ 1 then
    pure ({ pad2, nrResponseHeaderMeComp, orderId, clOrdId, securityId, execId, leavesQty, cxlQty, ordStatus, execType, execRestatementReason, crossedIndicator, productComplex, triggered, transactionDelayIndicator, pad7, orderEventGrpComp := ⟨orderEventGrpComp_, fits_orderEventGrpComp⟩ }, bytes)
  else none

theorem encode_length_pos (message : NewOrderNrResponse) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : NewOrderNrResponse) : (encode message).length ≤ 6234 := by
  have bound_orderEventGrpComp := message.orderEventGrpComp.length_lt
  unfold encode
  simp only [List.length_append, Alpha.encode_length, NrResponseHeaderMeComp.encode_length, encodeUIntLE_length, OrdStatus.encode_length, ExecType.encode_length, encodeUInt_length, encodeMany_length_const OrderEventGrpComp.encode 24 OrderEventGrpComp.encode_length]
  omega

@[simp] theorem decode_encode (message : NewOrderNrResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [NrResponseHeaderMeComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [OrdStatus.decode_encode]
  simp only [Option.bind_some]
  rw [ExecType.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 OrderEventGrpComp.encode OrderEventGrpComp.decode OrderEventGrpComp.decode_encode]
  simp only [Option.bind_some]
  simp only [message.orderEventGrpComp.length_lt, ↓reduceDIte]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : NewOrderNrResponse) : decode (encode message) = some (message, []) := by
  have trailing := decode_encode message []
  rw [List.append_nil] at trailing
  exact trailing

end NewOrderNrResponse

/-- New Order Response -/
structure NewOrderResponse where
  pad2 : Alpha 2
  responseHeaderMeComp : ResponseHeaderMeComp
  orderId : BitVec 64
  clOrdId : BitVec 64
  securityId : BitVec 64
  execId : BitVec 64
  leavesQty : BitVec 64
  cxlQty : BitVec 64
  trdRegTsEntryTime : BitVec 64
  trdRegTsTimePriority : BitVec 64
  ordStatus : OrdStatus
  execType : ExecType
  execRestatementReason : BitVec 16
  crossedIndicator : BitVec 8
  productComplex : BitVec 8
  triggered : BitVec 8
  transactionDelayIndicator : BitVec 8
  pad7 : Alpha 7
  orderEventGrpComp : Bounded 1 OrderEventGrpComp
  deriving DecidableEq, Repr

namespace NewOrderResponse

def encode (message : NewOrderResponse) : List UInt8 :=
  Alpha.encode message.pad2
    ++ ResponseHeaderMeComp.encode message.responseHeaderMeComp
    ++ encodeUIntLE 8 message.orderId
    ++ encodeUIntLE 8 message.clOrdId
    ++ encodeUIntLE 8 message.securityId
    ++ encodeUIntLE 8 message.execId
    ++ encodeUIntLE 8 message.leavesQty
    ++ encodeUIntLE 8 message.cxlQty
    ++ encodeUIntLE 8 message.trdRegTsEntryTime
    ++ encodeUIntLE 8 message.trdRegTsTimePriority
    ++ OrdStatus.encode message.ordStatus
    ++ ExecType.encode message.execType
    ++ encodeUIntLE 2 message.execRestatementReason
    ++ encodeUInt 1 message.crossedIndicator
    ++ encodeUInt 1 message.productComplex
    ++ encodeUInt 1 message.triggered
    ++ encodeUInt 1 message.transactionDelayIndicator
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.orderEventGrpComp.val.length)
    ++ Alpha.encode message.pad7
    ++ encodeMany OrderEventGrpComp.encode message.orderEventGrpComp.val

def decode (bytes : List UInt8) : Option (NewOrderResponse × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (responseHeaderMeComp, bytes) ← ResponseHeaderMeComp.decode bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  let (leavesQty, bytes) ← decodeUIntLE 8 bytes
  let (cxlQty, bytes) ← decodeUIntLE 8 bytes
  let (trdRegTsEntryTime, bytes) ← decodeUIntLE 8 bytes
  let (trdRegTsTimePriority, bytes) ← decodeUIntLE 8 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (execRestatementReason, bytes) ← decodeUIntLE 2 bytes
  let (crossedIndicator, bytes) ← decodeUInt 1 bytes
  let (productComplex, bytes) ← decodeUInt 1 bytes
  let (triggered, bytes) ← decodeUInt 1 bytes
  let (transactionDelayIndicator, bytes) ← decodeUInt 1 bytes
  let (noOrderEvents, bytes) ← decodeUInt 1 bytes
  let (pad7, bytes) ← Alpha.decode 7 bytes
  let (orderEventGrpComp_, bytes) ← decodeMany OrderEventGrpComp.decode noOrderEvents.toNat bytes
  if fits_orderEventGrpComp : orderEventGrpComp_.length < 256 ^ 1 then
    pure ({ pad2, responseHeaderMeComp, orderId, clOrdId, securityId, execId, leavesQty, cxlQty, trdRegTsEntryTime, trdRegTsTimePriority, ordStatus, execType, execRestatementReason, crossedIndicator, productComplex, triggered, transactionDelayIndicator, pad7, orderEventGrpComp := ⟨orderEventGrpComp_, fits_orderEventGrpComp⟩ }, bytes)
  else none

theorem encode_length_pos (message : NewOrderResponse) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : NewOrderResponse) : (encode message).length ≤ 6266 := by
  have bound_orderEventGrpComp := message.orderEventGrpComp.length_lt
  unfold encode
  simp only [List.length_append, Alpha.encode_length, ResponseHeaderMeComp.encode_length, encodeUIntLE_length, OrdStatus.encode_length, ExecType.encode_length, encodeUInt_length, encodeMany_length_const OrderEventGrpComp.encode 24 OrderEventGrpComp.encode_length]
  omega

@[simp] theorem decode_encode (message : NewOrderResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [ResponseHeaderMeComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [OrdStatus.decode_encode]
  simp only [Option.bind_some]
  rw [ExecType.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 OrderEventGrpComp.encode OrderEventGrpComp.decode OrderEventGrpComp.decode_encode]
  simp only [Option.bind_some]
  simp only [message.orderEventGrpComp.length_lt, ↓reduceDIte]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : NewOrderResponse) : decode (encode message) = some (message, []) := by
  have trailing := decode_encode message []
  rw [List.append_nil] at trailing
  exact trailing

end NewOrderResponse

/-- News Broadcast -/
structure NewsBroadcast where
  pad2 : Alpha 2
  rbcHeaderComp : RbcHeaderComp
  origTime : BitVec 64
  headline : Alpha 256
  varText : Bounded 2 UInt8
  alignmentPadding : Capped 4282374239
  deriving DecidableEq, Repr

namespace NewsBroadcast

def encode (message : NewsBroadcast) : List UInt8 :=
  Alpha.encode message.pad2
    ++ RbcHeaderComp.encode message.rbcHeaderComp
    ++ encodeUIntLE 8 message.origTime
    ++ encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.varText.val.length)
    ++ Alpha.encode message.headline
    ++ encodeMany Byte.encode message.varText.val
    ++ message.alignmentPadding.val

def decode (bytes : List UInt8) : Option NewsBroadcast := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderComp, bytes) ← RbcHeaderComp.decode bytes
  let (origTime, bytes) ← decodeUIntLE 8 bytes
  let (varTextLen, bytes) ← decodeUIntLE 2 bytes
  let (headline, bytes) ← Alpha.decode 256 bytes
  let (varText_, bytes) ← decodeMany Byte.decode varTextLen.toNat bytes
  let alignmentPadding_ := bytes
  if fits_varText : varText_.length < 256 ^ 2 then
    if fits_alignmentPadding : alignmentPadding_.length ≤ 4282374239 then
      pure { pad2, rbcHeaderComp, origTime, headline, varText := ⟨varText_, fits_varText⟩, alignmentPadding := ⟨alignmentPadding_, fits_alignmentPadding⟩ }
    else none
  else none

theorem encode_length_pos (message : NewsBroadcast) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : NewsBroadcast) : (encode message).length ≤ 4282440074 := by
  have bound_varText := message.varText.length_lt
  have bound_alignmentPadding := message.alignmentPadding.length_le
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RbcHeaderComp.encode_length, encodeUIntLE_length, encodeMany_length_const Byte.encode 1 Byte.encode_length]
  omega

theorem decode_encode (message : NewsBroadcast) : decode (encode message) = some message := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [RbcHeaderComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 2 Byte.encode Byte.decode Byte.decode_encode]
  simp only [Option.bind_some]
  simp only [message.varText.length_lt, message.alignmentPadding.length_le, ↓reduceDIte]
  rfl

end NewsBroadcast

/-- Order Exec Notification -/
structure OrderExecNotification where
  pad2 : Alpha 2
  rbcHeaderMeComp : RbcHeaderMeComp
  orderId : BitVec 64
  clOrdId : BitVec 64
  origClOrdId : BitVec 64
  securityId : BitVec 64
  execId : BitVec 64
  leavesQty : BitVec 64
  cumQty : BitVec 64
  cxlQty : BitVec 64
  marketSegmentId : BitVec 32
  massOrderReportId : BitVec 32
  execRestatementReason : BitVec 16
  side : BitVec 8
  productComplex : BitVec 8
  ordStatus : OrdStatus
  execType : ExecType
  triggered : BitVec 8
  crossedIndicator : BitVec 8
  fixClOrdId : Alpha 20
  fillsGrpComp : Bounded 1 FillsGrpComp
  instrmntLegExecGrpComp : Bounded 2 InstrmntLegExecGrpComp
  orderEventGrpComp : Bounded 1 OrderEventGrpComp
  deriving DecidableEq, Repr

namespace OrderExecNotification

def encode (message : OrderExecNotification) : List UInt8 :=
  Alpha.encode message.pad2
    ++ RbcHeaderMeComp.encode message.rbcHeaderMeComp
    ++ encodeUIntLE 8 message.orderId
    ++ encodeUIntLE 8 message.clOrdId
    ++ encodeUIntLE 8 message.origClOrdId
    ++ encodeUIntLE 8 message.securityId
    ++ encodeUIntLE 8 message.execId
    ++ encodeUIntLE 8 message.leavesQty
    ++ encodeUIntLE 8 message.cumQty
    ++ encodeUIntLE 8 message.cxlQty
    ++ encodeUIntLE 4 message.marketSegmentId
    ++ encodeUIntLE 4 message.massOrderReportId
    ++ encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.instrmntLegExecGrpComp.val.length)
    ++ encodeUIntLE 2 message.execRestatementReason
    ++ encodeUInt 1 message.side
    ++ encodeUInt 1 message.productComplex
    ++ OrdStatus.encode message.ordStatus
    ++ ExecType.encode message.execType
    ++ encodeUInt 1 message.triggered
    ++ encodeUInt 1 message.crossedIndicator
    ++ Alpha.encode message.fixClOrdId
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.fillsGrpComp.val.length)
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.orderEventGrpComp.val.length)
    ++ encodeMany FillsGrpComp.encode message.fillsGrpComp.val
    ++ encodeMany InstrmntLegExecGrpComp.encode message.instrmntLegExecGrpComp.val
    ++ encodeMany OrderEventGrpComp.encode message.orderEventGrpComp.val

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (OrderExecNotification × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderMeComp, bytes) ← RbcHeaderMeComp.decode bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (origClOrdId, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  let (leavesQty, bytes) ← decodeUIntLE 8 bytes
  let (cumQty, bytes) ← decodeUIntLE 8 bytes
  let (cxlQty, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (massOrderReportId, bytes) ← decodeUIntLE 4 bytes
  let (noLegExecs, bytes) ← decodeUIntLE 2 bytes
  let (execRestatementReason, bytes) ← decodeUIntLE 2 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (productComplex, bytes) ← decodeUInt 1 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (triggered, bytes) ← decodeUInt 1 bytes
  let (crossedIndicator, bytes) ← decodeUInt 1 bytes
  let (fixClOrdId, bytes) ← Alpha.decode 20 bytes
  let (noFills, bytes) ← decodeUInt 1 bytes
  let (noOrderEvents, bytes) ← decodeUInt 1 bytes
  let (fillsGrpComp_, bytes) ← decodeMany FillsGrpComp.decode noFills.toNat bytes
  let (instrmntLegExecGrpComp_, bytes) ← decodeMany InstrmntLegExecGrpComp.decode noLegExecs.toNat bytes
  let (orderEventGrpComp_, bytes) ← decodeMany OrderEventGrpComp.decode noOrderEvents.toNat bytes
  if fits_fillsGrpComp : fillsGrpComp_.length < 256 ^ 1 then
    if fits_instrmntLegExecGrpComp : instrmntLegExecGrpComp_.length < 256 ^ 2 then
      if fits_orderEventGrpComp : orderEventGrpComp_.length < 256 ^ 1 then
        pure ({ pad2, rbcHeaderMeComp, orderId, clOrdId, origClOrdId, securityId, execId, leavesQty, cumQty, cxlQty, marketSegmentId, massOrderReportId, execRestatementReason, side, productComplex, ordStatus, execType, triggered, crossedIndicator, fixClOrdId, fillsGrpComp := ⟨fillsGrpComp_, fits_fillsGrpComp⟩, instrmntLegExecGrpComp := ⟨instrmntLegExecGrpComp_, fits_instrmntLegExecGrpComp⟩, orderEventGrpComp := ⟨orderEventGrpComp_, fits_orderEventGrpComp⟩ }, bytes)
      else none
    else none
  else none

theorem encode_length_pos (message : OrderExecNotification) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : OrderExecNotification) : (encode message).length ≤ 2111562 := by
  have bound_fillsGrpComp := message.fillsGrpComp.length_lt
  have bound_instrmntLegExecGrpComp := message.instrmntLegExecGrpComp.length_lt
  have bound_orderEventGrpComp := message.orderEventGrpComp.length_lt
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RbcHeaderMeComp.encode_length, encodeUIntLE_length, encodeUInt_length, OrdStatus.encode_length, ExecType.encode_length, encodeMany_length_const FillsGrpComp.encode 32 FillsGrpComp.encode_length, encodeMany_length_const InstrmntLegExecGrpComp.encode 32 InstrmntLegExecGrpComp.encode_length, encodeMany_length_const OrderEventGrpComp.encode 24 OrderEventGrpComp.encode_length]
  omega

@[simp] theorem decode_encode (message : OrderExecNotification) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [RbcHeaderMeComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [OrdStatus.decode_encode]
  simp only [Option.bind_some]
  rw [ExecType.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 FillsGrpComp.encode FillsGrpComp.decode FillsGrpComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 2 InstrmntLegExecGrpComp.encode InstrmntLegExecGrpComp.decode InstrmntLegExecGrpComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 OrderEventGrpComp.encode OrderEventGrpComp.decode OrderEventGrpComp.decode_encode]
  simp only [Option.bind_some]
  simp only [message.fillsGrpComp.length_lt, message.instrmntLegExecGrpComp.length_lt, message.orderEventGrpComp.length_lt, ↓reduceDIte]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : OrderExecNotification) : decode (encode message) = some (message, []) := by
  have trailing := decode_encode message []
  rw [List.append_nil] at trailing
  exact trailing

end OrderExecNotification

/-- Leg Ord Grp Comp: 8 bytes -/
structure LegOrdGrpComp where
  legAccount : Alpha 2
  legPositionEffect : LegPositionEffect
  pad5 : Alpha 5
  deriving DecidableEq, Repr

namespace LegOrdGrpComp

def encode (message : LegOrdGrpComp) : List UInt8 :=
  Alpha.encode message.legAccount
    ++ LegPositionEffect.encode message.legPositionEffect
    ++ Alpha.encode message.pad5

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
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [LegPositionEffect.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end LegOrdGrpComp

/-- Order Exec Report Broadcast -/
structure OrderExecReportBroadcast where
  pad2 : Alpha 2
  rbcHeaderMeComp : RbcHeaderMeComp
  orderId : BitVec 64
  clOrdId : BitVec 64
  origClOrdId : BitVec 64
  securityId : BitVec 64
  execId : BitVec 64
  trdRegTsEntryTime : BitVec 64
  trdRegTsTimePriority : BitVec 64
  price : BitVec 64
  leavesQty : BitVec 64
  cumQty : BitVec 64
  cxlQty : BitVec 64
  orderQty : BitVec 64
  stopPx : BitVec 64
  marketSegmentId : BitVec 32
  massOrderReportId : BitVec 32
  expireDate : BitVec 32
  matchInstCrossId : BitVec 32
  partyIdExecutingUnit : BitVec 32
  partyIdSessionId : BitVec 32
  partyIdExecutingTrader : BitVec 32
  partyIdEnteringTrader : BitVec 32
  execRestatementReason : BitVec 16
  partyIdEnteringFirm : BitVec 8
  selfMatchPreventionInstruction : BitVec 8
  productComplex : BitVec 8
  ordStatus : OrdStatus
  execType : ExecType
  side : BitVec 8
  ordType : BitVec 8
  tradingCapacity : BitVec 8
  timeInForce : BitVec 8
  execInst : BitVec 8
  tradingSessionSubId : BitVec 8
  applSeqIndicator : BitVec 8
  account : Alpha 2
  partyIdPositionAccount : Alpha 32
  positionEffect : PositionEffect
  partyIdTakeUpTradingFirm : Alpha 5
  partyIdOrderOriginationFirm : Alpha 7
  partyIdBeneficiary : Alpha 9
  partyIdLocationId : Alpha 2
  custOrderHandlingInst : CustOrderHandlingInst
  complianceText : Alpha 20
  freeText1 : Alpha 12
  freeText2 : Alpha 12
  freeText3 : Alpha 12
  fixClOrdId : Alpha 20
  triggered : BitVec 8
  crossedIndicator : BitVec 8
  pad4 : Alpha 4
  legOrdGrpComp : Bounded 1 LegOrdGrpComp
  fillsGrpComp : Bounded 1 FillsGrpComp
  instrmntLegExecGrpComp : Bounded 2 InstrmntLegExecGrpComp
  orderEventGrpComp : Bounded 1 OrderEventGrpComp
  deriving DecidableEq, Repr

namespace OrderExecReportBroadcast

def encode (message : OrderExecReportBroadcast) : List UInt8 :=
  Alpha.encode message.pad2
    ++ RbcHeaderMeComp.encode message.rbcHeaderMeComp
    ++ encodeUIntLE 8 message.orderId
    ++ encodeUIntLE 8 message.clOrdId
    ++ encodeUIntLE 8 message.origClOrdId
    ++ encodeUIntLE 8 message.securityId
    ++ encodeUIntLE 8 message.execId
    ++ encodeUIntLE 8 message.trdRegTsEntryTime
    ++ encodeUIntLE 8 message.trdRegTsTimePriority
    ++ encodeUIntLE 8 message.price
    ++ encodeUIntLE 8 message.leavesQty
    ++ encodeUIntLE 8 message.cumQty
    ++ encodeUIntLE 8 message.cxlQty
    ++ encodeUIntLE 8 message.orderQty
    ++ encodeUIntLE 8 message.stopPx
    ++ encodeUIntLE 4 message.marketSegmentId
    ++ encodeUIntLE 4 message.massOrderReportId
    ++ encodeUIntLE 4 message.expireDate
    ++ encodeUIntLE 4 message.matchInstCrossId
    ++ encodeUIntLE 4 message.partyIdExecutingUnit
    ++ encodeUIntLE 4 message.partyIdSessionId
    ++ encodeUIntLE 4 message.partyIdExecutingTrader
    ++ encodeUIntLE 4 message.partyIdEnteringTrader
    ++ encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.instrmntLegExecGrpComp.val.length)
    ++ encodeUIntLE 2 message.execRestatementReason
    ++ encodeUInt 1 message.partyIdEnteringFirm
    ++ encodeUInt 1 message.selfMatchPreventionInstruction
    ++ encodeUInt 1 message.productComplex
    ++ OrdStatus.encode message.ordStatus
    ++ ExecType.encode message.execType
    ++ encodeUInt 1 message.side
    ++ encodeUInt 1 message.ordType
    ++ encodeUInt 1 message.tradingCapacity
    ++ encodeUInt 1 message.timeInForce
    ++ encodeUInt 1 message.execInst
    ++ encodeUInt 1 message.tradingSessionSubId
    ++ encodeUInt 1 message.applSeqIndicator
    ++ Alpha.encode message.account
    ++ Alpha.encode message.partyIdPositionAccount
    ++ PositionEffect.encode message.positionEffect
    ++ Alpha.encode message.partyIdTakeUpTradingFirm
    ++ Alpha.encode message.partyIdOrderOriginationFirm
    ++ Alpha.encode message.partyIdBeneficiary
    ++ Alpha.encode message.partyIdLocationId
    ++ CustOrderHandlingInst.encode message.custOrderHandlingInst
    ++ Alpha.encode message.complianceText
    ++ Alpha.encode message.freeText1
    ++ Alpha.encode message.freeText2
    ++ Alpha.encode message.freeText3
    ++ Alpha.encode message.fixClOrdId
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.fillsGrpComp.val.length)
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.legOrdGrpComp.val.length)
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.orderEventGrpComp.val.length)
    ++ encodeUInt 1 message.triggered
    ++ encodeUInt 1 message.crossedIndicator
    ++ Alpha.encode message.pad4
    ++ encodeMany LegOrdGrpComp.encode message.legOrdGrpComp.val
    ++ encodeMany FillsGrpComp.encode message.fillsGrpComp.val
    ++ encodeMany InstrmntLegExecGrpComp.encode message.instrmntLegExecGrpComp.val
    ++ encodeMany OrderEventGrpComp.encode message.orderEventGrpComp.val

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (OrderExecReportBroadcast × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderMeComp, bytes) ← RbcHeaderMeComp.decode bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (origClOrdId, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  let (trdRegTsEntryTime, bytes) ← decodeUIntLE 8 bytes
  let (trdRegTsTimePriority, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (leavesQty, bytes) ← decodeUIntLE 8 bytes
  let (cumQty, bytes) ← decodeUIntLE 8 bytes
  let (cxlQty, bytes) ← decodeUIntLE 8 bytes
  let (orderQty, bytes) ← decodeUIntLE 8 bytes
  let (stopPx, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (massOrderReportId, bytes) ← decodeUIntLE 4 bytes
  let (expireDate, bytes) ← decodeUIntLE 4 bytes
  let (matchInstCrossId, bytes) ← decodeUIntLE 4 bytes
  let (partyIdExecutingUnit, bytes) ← decodeUIntLE 4 bytes
  let (partyIdSessionId, bytes) ← decodeUIntLE 4 bytes
  let (partyIdExecutingTrader, bytes) ← decodeUIntLE 4 bytes
  let (partyIdEnteringTrader, bytes) ← decodeUIntLE 4 bytes
  let (noLegExecs, bytes) ← decodeUIntLE 2 bytes
  let (execRestatementReason, bytes) ← decodeUIntLE 2 bytes
  let (partyIdEnteringFirm, bytes) ← decodeUInt 1 bytes
  let (selfMatchPreventionInstruction, bytes) ← decodeUInt 1 bytes
  let (productComplex, bytes) ← decodeUInt 1 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (ordType, bytes) ← decodeUInt 1 bytes
  let (tradingCapacity, bytes) ← decodeUInt 1 bytes
  let (timeInForce, bytes) ← decodeUInt 1 bytes
  let (execInst, bytes) ← decodeUInt 1 bytes
  let (tradingSessionSubId, bytes) ← decodeUInt 1 bytes
  let (applSeqIndicator, bytes) ← decodeUInt 1 bytes
  let (account, bytes) ← Alpha.decode 2 bytes
  let (partyIdPositionAccount, bytes) ← Alpha.decode 32 bytes
  let (positionEffect, bytes) ← PositionEffect.decode bytes
  let (partyIdTakeUpTradingFirm, bytes) ← Alpha.decode 5 bytes
  let (partyIdOrderOriginationFirm, bytes) ← Alpha.decode 7 bytes
  let (partyIdBeneficiary, bytes) ← Alpha.decode 9 bytes
  let (partyIdLocationId, bytes) ← Alpha.decode 2 bytes
  let (custOrderHandlingInst, bytes) ← CustOrderHandlingInst.decode bytes
  let (complianceText, bytes) ← Alpha.decode 20 bytes
  let (freeText1, bytes) ← Alpha.decode 12 bytes
  let (freeText2, bytes) ← Alpha.decode 12 bytes
  let (freeText3, bytes) ← Alpha.decode 12 bytes
  let (fixClOrdId, bytes) ← Alpha.decode 20 bytes
  let (noFills, bytes) ← decodeUInt 1 bytes
  let (noLegOnbooks, bytes) ← decodeUInt 1 bytes
  let (noOrderEvents, bytes) ← decodeUInt 1 bytes
  let (triggered, bytes) ← decodeUInt 1 bytes
  let (crossedIndicator, bytes) ← decodeUInt 1 bytes
  let (pad4, bytes) ← Alpha.decode 4 bytes
  let (legOrdGrpComp_, bytes) ← decodeMany LegOrdGrpComp.decode noLegOnbooks.toNat bytes
  let (fillsGrpComp_, bytes) ← decodeMany FillsGrpComp.decode noFills.toNat bytes
  let (instrmntLegExecGrpComp_, bytes) ← decodeMany InstrmntLegExecGrpComp.decode noLegExecs.toNat bytes
  let (orderEventGrpComp_, bytes) ← decodeMany OrderEventGrpComp.decode noOrderEvents.toNat bytes
  if fits_legOrdGrpComp : legOrdGrpComp_.length < 256 ^ 1 then
    if fits_fillsGrpComp : fillsGrpComp_.length < 256 ^ 1 then
      if fits_instrmntLegExecGrpComp : instrmntLegExecGrpComp_.length < 256 ^ 2 then
        if fits_orderEventGrpComp : orderEventGrpComp_.length < 256 ^ 1 then
          pure ({ pad2, rbcHeaderMeComp, orderId, clOrdId, origClOrdId, securityId, execId, trdRegTsEntryTime, trdRegTsTimePriority, price, leavesQty, cumQty, cxlQty, orderQty, stopPx, marketSegmentId, massOrderReportId, expireDate, matchInstCrossId, partyIdExecutingUnit, partyIdSessionId, partyIdExecutingTrader, partyIdEnteringTrader, execRestatementReason, partyIdEnteringFirm, selfMatchPreventionInstruction, productComplex, ordStatus, execType, side, ordType, tradingCapacity, timeInForce, execInst, tradingSessionSubId, applSeqIndicator, account, partyIdPositionAccount, positionEffect, partyIdTakeUpTradingFirm, partyIdOrderOriginationFirm, partyIdBeneficiary, partyIdLocationId, custOrderHandlingInst, complianceText, freeText1, freeText2, freeText3, fixClOrdId, triggered, crossedIndicator, pad4, legOrdGrpComp := ⟨legOrdGrpComp_, fits_legOrdGrpComp⟩, fillsGrpComp := ⟨fillsGrpComp_, fits_fillsGrpComp⟩, instrmntLegExecGrpComp := ⟨instrmntLegExecGrpComp_, fits_instrmntLegExecGrpComp⟩, orderEventGrpComp := ⟨orderEventGrpComp_, fits_orderEventGrpComp⟩ }, bytes)
        else none
      else none
    else none
  else none

theorem encode_length_pos (message : OrderExecReportBroadcast) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : OrderExecReportBroadcast) : (encode message).length ≤ 2113794 := by
  have bound_legOrdGrpComp := message.legOrdGrpComp.length_lt
  have bound_fillsGrpComp := message.fillsGrpComp.length_lt
  have bound_instrmntLegExecGrpComp := message.instrmntLegExecGrpComp.length_lt
  have bound_orderEventGrpComp := message.orderEventGrpComp.length_lt
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RbcHeaderMeComp.encode_length, encodeUIntLE_length, encodeUInt_length, OrdStatus.encode_length, ExecType.encode_length, PositionEffect.encode_length, CustOrderHandlingInst.encode_length, encodeMany_length_const LegOrdGrpComp.encode 8 LegOrdGrpComp.encode_length, encodeMany_length_const FillsGrpComp.encode 32 FillsGrpComp.encode_length, encodeMany_length_const InstrmntLegExecGrpComp.encode 32 InstrmntLegExecGrpComp.encode_length, encodeMany_length_const OrderEventGrpComp.encode 24 OrderEventGrpComp.encode_length]
  omega

@[simp] theorem decode_encode (message : OrderExecReportBroadcast) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [RbcHeaderMeComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [OrdStatus.decode_encode]
  simp only [Option.bind_some]
  rw [ExecType.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [PositionEffect.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [CustOrderHandlingInst.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 LegOrdGrpComp.encode LegOrdGrpComp.decode LegOrdGrpComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 FillsGrpComp.encode FillsGrpComp.decode FillsGrpComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 2 InstrmntLegExecGrpComp.encode InstrmntLegExecGrpComp.decode InstrmntLegExecGrpComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 OrderEventGrpComp.encode OrderEventGrpComp.decode OrderEventGrpComp.decode_encode]
  simp only [Option.bind_some]
  simp only [message.legOrdGrpComp.length_lt, message.fillsGrpComp.length_lt, message.instrmntLegExecGrpComp.length_lt, message.orderEventGrpComp.length_lt, ↓reduceDIte]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : OrderExecReportBroadcast) : decode (encode message) = some (message, []) := by
  have trailing := decode_encode message []
  rw [List.append_nil] at trailing
  exact trailing

end OrderExecReportBroadcast

/-- Order Exec Response -/
structure OrderExecResponse where
  pad2 : Alpha 2
  responseHeaderMeComp : ResponseHeaderMeComp
  orderId : BitVec 64
  clOrdId : BitVec 64
  origClOrdId : BitVec 64
  securityId : BitVec 64
  execId : BitVec 64
  trdRegTsEntryTime : BitVec 64
  trdRegTsTimePriority : BitVec 64
  leavesQty : BitVec 64
  cumQty : BitVec 64
  cxlQty : BitVec 64
  marketSegmentId : BitVec 32
  execRestatementReason : BitVec 16
  side : BitVec 8
  productComplex : BitVec 8
  ordStatus : OrdStatus
  execType : ExecType
  triggered : BitVec 8
  crossedIndicator : BitVec 8
  transactionDelayIndicator : BitVec 8
  pad7 : Alpha 7
  fillsGrpComp : Bounded 1 FillsGrpComp
  instrmntLegExecGrpComp : Bounded 2 InstrmntLegExecGrpComp
  orderEventGrpComp : Bounded 1 OrderEventGrpComp
  deriving DecidableEq, Repr

namespace OrderExecResponse

def encode (message : OrderExecResponse) : List UInt8 :=
  Alpha.encode message.pad2
    ++ ResponseHeaderMeComp.encode message.responseHeaderMeComp
    ++ encodeUIntLE 8 message.orderId
    ++ encodeUIntLE 8 message.clOrdId
    ++ encodeUIntLE 8 message.origClOrdId
    ++ encodeUIntLE 8 message.securityId
    ++ encodeUIntLE 8 message.execId
    ++ encodeUIntLE 8 message.trdRegTsEntryTime
    ++ encodeUIntLE 8 message.trdRegTsTimePriority
    ++ encodeUIntLE 8 message.leavesQty
    ++ encodeUIntLE 8 message.cumQty
    ++ encodeUIntLE 8 message.cxlQty
    ++ encodeUIntLE 4 message.marketSegmentId
    ++ encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.instrmntLegExecGrpComp.val.length)
    ++ encodeUIntLE 2 message.execRestatementReason
    ++ encodeUInt 1 message.side
    ++ encodeUInt 1 message.productComplex
    ++ OrdStatus.encode message.ordStatus
    ++ ExecType.encode message.execType
    ++ encodeUInt 1 message.triggered
    ++ encodeUInt 1 message.crossedIndicator
    ++ encodeUInt 1 message.transactionDelayIndicator
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.fillsGrpComp.val.length)
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.orderEventGrpComp.val.length)
    ++ Alpha.encode message.pad7
    ++ encodeMany FillsGrpComp.encode message.fillsGrpComp.val
    ++ encodeMany InstrmntLegExecGrpComp.encode message.instrmntLegExecGrpComp.val
    ++ encodeMany OrderEventGrpComp.encode message.orderEventGrpComp.val

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (OrderExecResponse × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (responseHeaderMeComp, bytes) ← ResponseHeaderMeComp.decode bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (origClOrdId, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  let (trdRegTsEntryTime, bytes) ← decodeUIntLE 8 bytes
  let (trdRegTsTimePriority, bytes) ← decodeUIntLE 8 bytes
  let (leavesQty, bytes) ← decodeUIntLE 8 bytes
  let (cumQty, bytes) ← decodeUIntLE 8 bytes
  let (cxlQty, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (noLegExecs, bytes) ← decodeUIntLE 2 bytes
  let (execRestatementReason, bytes) ← decodeUIntLE 2 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (productComplex, bytes) ← decodeUInt 1 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (triggered, bytes) ← decodeUInt 1 bytes
  let (crossedIndicator, bytes) ← decodeUInt 1 bytes
  let (transactionDelayIndicator, bytes) ← decodeUInt 1 bytes
  let (noFills, bytes) ← decodeUInt 1 bytes
  let (noOrderEvents, bytes) ← decodeUInt 1 bytes
  let (pad7, bytes) ← Alpha.decode 7 bytes
  let (fillsGrpComp_, bytes) ← decodeMany FillsGrpComp.decode noFills.toNat bytes
  let (instrmntLegExecGrpComp_, bytes) ← decodeMany InstrmntLegExecGrpComp.decode noLegExecs.toNat bytes
  let (orderEventGrpComp_, bytes) ← decodeMany OrderEventGrpComp.decode noOrderEvents.toNat bytes
  if fits_fillsGrpComp : fillsGrpComp_.length < 256 ^ 1 then
    if fits_instrmntLegExecGrpComp : instrmntLegExecGrpComp_.length < 256 ^ 2 then
      if fits_orderEventGrpComp : orderEventGrpComp_.length < 256 ^ 1 then
        pure ({ pad2, responseHeaderMeComp, orderId, clOrdId, origClOrdId, securityId, execId, trdRegTsEntryTime, trdRegTsTimePriority, leavesQty, cumQty, cxlQty, marketSegmentId, execRestatementReason, side, productComplex, ordStatus, execType, triggered, crossedIndicator, transactionDelayIndicator, pad7, fillsGrpComp := ⟨fillsGrpComp_, fits_fillsGrpComp⟩, instrmntLegExecGrpComp := ⟨instrmntLegExecGrpComp_, fits_instrmntLegExecGrpComp⟩, orderEventGrpComp := ⟨orderEventGrpComp_, fits_orderEventGrpComp⟩ }, bytes)
      else none
    else none
  else none

theorem encode_length_pos (message : OrderExecResponse) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : OrderExecResponse) : (encode message).length ≤ 2111570 := by
  have bound_fillsGrpComp := message.fillsGrpComp.length_lt
  have bound_instrmntLegExecGrpComp := message.instrmntLegExecGrpComp.length_lt
  have bound_orderEventGrpComp := message.orderEventGrpComp.length_lt
  unfold encode
  simp only [List.length_append, Alpha.encode_length, ResponseHeaderMeComp.encode_length, encodeUIntLE_length, encodeUInt_length, OrdStatus.encode_length, ExecType.encode_length, encodeMany_length_const FillsGrpComp.encode 32 FillsGrpComp.encode_length, encodeMany_length_const InstrmntLegExecGrpComp.encode 32 InstrmntLegExecGrpComp.encode_length, encodeMany_length_const OrderEventGrpComp.encode 24 OrderEventGrpComp.encode_length]
  omega

@[simp] theorem decode_encode (message : OrderExecResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [ResponseHeaderMeComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [OrdStatus.decode_encode]
  simp only [Option.bind_some]
  rw [ExecType.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 FillsGrpComp.encode FillsGrpComp.decode FillsGrpComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 2 InstrmntLegExecGrpComp.encode InstrmntLegExecGrpComp.decode InstrmntLegExecGrpComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 OrderEventGrpComp.encode OrderEventGrpComp.decode OrderEventGrpComp.decode_encode]
  simp only [Option.bind_some]
  simp only [message.fillsGrpComp.length_lt, message.instrmntLegExecGrpComp.length_lt, message.orderEventGrpComp.length_lt, ↓reduceDIte]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : OrderExecResponse) : decode (encode message) = some (message, []) := by
  have trailing := decode_encode message []
  rw [List.append_nil] at trailing
  exact trailing

end OrderExecResponse

/-- Party Action Report: 66 bytes -/
structure PartyActionReport where
  pad2 : Alpha 2
  rbcHeaderComp : RbcHeaderComp
  transactTime : BitVec 64
  tradeDate : BitVec 32
  requestingPartyIdExecutingTrader : BitVec 32
  partyIdExecutingUnit : BitVec 32
  partyIdExecutingTrader : BitVec 32
  requestingPartyIdExecutingSystem : BitVec 32
  marketId : BitVec 16
  partyActionType : BitVec 8
  requestingPartyIdEnteringFirm : BitVec 8
  deriving DecidableEq, Repr

namespace PartyActionReport

def encode (message : PartyActionReport) : List UInt8 :=
  Alpha.encode message.pad2
    ++ RbcHeaderComp.encode message.rbcHeaderComp
    ++ encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 4 message.tradeDate
    ++ encodeUIntLE 4 message.requestingPartyIdExecutingTrader
    ++ encodeUIntLE 4 message.partyIdExecutingUnit
    ++ encodeUIntLE 4 message.partyIdExecutingTrader
    ++ encodeUIntLE 4 message.requestingPartyIdExecutingSystem
    ++ encodeUIntLE 2 message.marketId
    ++ encodeUInt 1 message.partyActionType
    ++ encodeUInt 1 message.requestingPartyIdEnteringFirm

def decode (bytes : List UInt8) : Option (PartyActionReport × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderComp, bytes) ← RbcHeaderComp.decode bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (tradeDate, bytes) ← decodeUIntLE 4 bytes
  let (requestingPartyIdExecutingTrader, bytes) ← decodeUIntLE 4 bytes
  let (partyIdExecutingUnit, bytes) ← decodeUIntLE 4 bytes
  let (partyIdExecutingTrader, bytes) ← decodeUIntLE 4 bytes
  let (requestingPartyIdExecutingSystem, bytes) ← decodeUIntLE 4 bytes
  let (marketId, bytes) ← decodeUIntLE 2 bytes
  let (partyActionType, bytes) ← decodeUInt 1 bytes
  let (requestingPartyIdEnteringFirm, bytes) ← decodeUInt 1 bytes
  pure ({ pad2, rbcHeaderComp, transactTime, tradeDate, requestingPartyIdExecutingTrader, partyIdExecutingUnit, partyIdExecutingTrader, requestingPartyIdExecutingSystem, marketId, partyActionType, requestingPartyIdEnteringFirm }, bytes)

@[simp] theorem encode_length (message : PartyActionReport) : (encode message).length = 66 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RbcHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : PartyActionReport) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PartyActionReport) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [RbcHeaderComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : PartyActionReport) : decode (encode message) = some (message, []) := by
  have trailing := decode_encode message []
  rw [List.append_nil] at trailing
  exact trailing

end PartyActionReport

/-- Party Entitlements Update Report: 82 bytes -/
structure PartyEntitlementsUpdateReport where
  pad2 : Alpha 2
  rbcHeaderComp : RbcHeaderComp
  transactTime : BitVec 64
  tradeDate : BitVec 32
  partyDetailIdExecutingUnit : BitVec 32
  requestingPartyIdExecutingSystem : BitVec 32
  marketId : BitVec 16
  listUpdateAction : ListUpdateAction
  requestingPartyEnteringFirm : Alpha 9
  requestingPartyClearingFirm : Alpha 9
  partyDetailStatus : BitVec 8
  pad6 : Alpha 6
  deriving DecidableEq, Repr

namespace PartyEntitlementsUpdateReport

def encode (message : PartyEntitlementsUpdateReport) : List UInt8 :=
  Alpha.encode message.pad2
    ++ RbcHeaderComp.encode message.rbcHeaderComp
    ++ encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 4 message.tradeDate
    ++ encodeUIntLE 4 message.partyDetailIdExecutingUnit
    ++ encodeUIntLE 4 message.requestingPartyIdExecutingSystem
    ++ encodeUIntLE 2 message.marketId
    ++ ListUpdateAction.encode message.listUpdateAction
    ++ Alpha.encode message.requestingPartyEnteringFirm
    ++ Alpha.encode message.requestingPartyClearingFirm
    ++ encodeUInt 1 message.partyDetailStatus
    ++ Alpha.encode message.pad6

def decode (bytes : List UInt8) : Option (PartyEntitlementsUpdateReport × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderComp, bytes) ← RbcHeaderComp.decode bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (tradeDate, bytes) ← decodeUIntLE 4 bytes
  let (partyDetailIdExecutingUnit, bytes) ← decodeUIntLE 4 bytes
  let (requestingPartyIdExecutingSystem, bytes) ← decodeUIntLE 4 bytes
  let (marketId, bytes) ← decodeUIntLE 2 bytes
  let (listUpdateAction, bytes) ← ListUpdateAction.decode bytes
  let (requestingPartyEnteringFirm, bytes) ← Alpha.decode 9 bytes
  let (requestingPartyClearingFirm, bytes) ← Alpha.decode 9 bytes
  let (partyDetailStatus, bytes) ← decodeUInt 1 bytes
  let (pad6, bytes) ← Alpha.decode 6 bytes
  pure ({ pad2, rbcHeaderComp, transactTime, tradeDate, partyDetailIdExecutingUnit, requestingPartyIdExecutingSystem, marketId, listUpdateAction, requestingPartyEnteringFirm, requestingPartyClearingFirm, partyDetailStatus, pad6 }, bytes)

@[simp] theorem encode_length (message : PartyEntitlementsUpdateReport) : (encode message).length = 82 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RbcHeaderComp.encode_length, encodeUIntLE_length, ListUpdateAction.encode_length, encodeUInt_length]

theorem encode_length_pos (message : PartyEntitlementsUpdateReport) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PartyEntitlementsUpdateReport) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [RbcHeaderComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [ListUpdateAction.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : PartyEntitlementsUpdateReport) : decode (encode message) = some (message, []) := by
  have trailing := decode_encode message []
  rw [List.append_nil] at trailing
  exact trailing

end PartyEntitlementsUpdateReport

/-- Ping Response: 58 bytes -/
structure PingResponse where
  pad2 : Alpha 2
  nrResponseHeaderMeComp : NrResponseHeaderMeComp
  transactTime : BitVec 64
  deriving DecidableEq, Repr

namespace PingResponse

def encode (message : PingResponse) : List UInt8 :=
  Alpha.encode message.pad2
    ++ NrResponseHeaderMeComp.encode message.nrResponseHeaderMeComp
    ++ encodeUIntLE 8 message.transactTime

def decode (bytes : List UInt8) : Option (PingResponse × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (nrResponseHeaderMeComp, bytes) ← NrResponseHeaderMeComp.decode bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  pure ({ pad2, nrResponseHeaderMeComp, transactTime }, bytes)

@[simp] theorem encode_length (message : PingResponse) : (encode message).length = 58 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, NrResponseHeaderMeComp.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : PingResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PingResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [NrResponseHeaderMeComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : PingResponse) : decode (encode message) = some (message, []) := by
  have trailing := decode_encode message []
  rw [List.append_nil] at trailing
  exact trailing

end PingResponse

/-- Risk Limits Rpt Grp Comp: 48 bytes -/
structure RiskLimitsRptGrpComp where
  riskLimitQty : BitVec 64
  riskLimitOpenQty : BitVec 64
  riskLimitNetPositionQty : BitVec 64
  nettingCoefficient : BitVec 64
  activationDate : BitVec 32
  riskLimitType : BitVec 8
  riskLimitRequestingPartyRole : BitVec 8
  riskLimitViolationIndicator : BitVec 8
  riskLimitGroup : Alpha 3
  pad6 : Alpha 6
  deriving DecidableEq, Repr

namespace RiskLimitsRptGrpComp

def encode (message : RiskLimitsRptGrpComp) : List UInt8 :=
  encodeUIntLE 8 message.riskLimitQty
    ++ encodeUIntLE 8 message.riskLimitOpenQty
    ++ encodeUIntLE 8 message.riskLimitNetPositionQty
    ++ encodeUIntLE 8 message.nettingCoefficient
    ++ encodeUIntLE 4 message.activationDate
    ++ encodeUInt 1 message.riskLimitType
    ++ encodeUInt 1 message.riskLimitRequestingPartyRole
    ++ encodeUInt 1 message.riskLimitViolationIndicator
    ++ Alpha.encode message.riskLimitGroup
    ++ Alpha.encode message.pad6

def decode (bytes : List UInt8) : Option (RiskLimitsRptGrpComp × List UInt8) := do
  let (riskLimitQty, bytes) ← decodeUIntLE 8 bytes
  let (riskLimitOpenQty, bytes) ← decodeUIntLE 8 bytes
  let (riskLimitNetPositionQty, bytes) ← decodeUIntLE 8 bytes
  let (nettingCoefficient, bytes) ← decodeUIntLE 8 bytes
  let (activationDate, bytes) ← decodeUIntLE 4 bytes
  let (riskLimitType, bytes) ← decodeUInt 1 bytes
  let (riskLimitRequestingPartyRole, bytes) ← decodeUInt 1 bytes
  let (riskLimitViolationIndicator, bytes) ← decodeUInt 1 bytes
  let (riskLimitGroup, bytes) ← Alpha.decode 3 bytes
  let (pad6, bytes) ← Alpha.decode 6 bytes
  pure ({ riskLimitQty, riskLimitOpenQty, riskLimitNetPositionQty, nettingCoefficient, activationDate, riskLimitType, riskLimitRequestingPartyRole, riskLimitViolationIndicator, riskLimitGroup, pad6 }, bytes)

@[simp] theorem encode_length (message : RiskLimitsRptGrpComp) : (encode message).length = 48 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : RiskLimitsRptGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RiskLimitsRptGrpComp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end RiskLimitsRptGrpComp

/-- Pre Trade Risk Limit Response -/
structure PreTradeRiskLimitResponse where
  pad2 : Alpha 2
  nrResponseHeaderMeComp : NrResponseHeaderMeComp
  riskLimitReportId : BitVec 64
  marketSegmentId : BitVec 32
  partyDetailStatus : BitVec 8
  riskLimitPlatform : BitVec 8
  partyDetailExecutingUnit : Alpha 5
  pad4 : Alpha 4
  riskLimitsRptGrpComp : Bounded 1 RiskLimitsRptGrpComp
  deriving DecidableEq, Repr

namespace PreTradeRiskLimitResponse

def encode (message : PreTradeRiskLimitResponse) : List UInt8 :=
  Alpha.encode message.pad2
    ++ NrResponseHeaderMeComp.encode message.nrResponseHeaderMeComp
    ++ encodeUIntLE 8 message.riskLimitReportId
    ++ encodeUIntLE 4 message.marketSegmentId
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.riskLimitsRptGrpComp.val.length)
    ++ encodeUInt 1 message.partyDetailStatus
    ++ encodeUInt 1 message.riskLimitPlatform
    ++ Alpha.encode message.partyDetailExecutingUnit
    ++ Alpha.encode message.pad4
    ++ encodeMany RiskLimitsRptGrpComp.encode message.riskLimitsRptGrpComp.val

def decode (bytes : List UInt8) : Option (PreTradeRiskLimitResponse × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (nrResponseHeaderMeComp, bytes) ← NrResponseHeaderMeComp.decode bytes
  let (riskLimitReportId, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (noRiskLimits, bytes) ← decodeUInt 1 bytes
  let (partyDetailStatus, bytes) ← decodeUInt 1 bytes
  let (riskLimitPlatform, bytes) ← decodeUInt 1 bytes
  let (partyDetailExecutingUnit, bytes) ← Alpha.decode 5 bytes
  let (pad4, bytes) ← Alpha.decode 4 bytes
  let (riskLimitsRptGrpComp_, bytes) ← decodeMany RiskLimitsRptGrpComp.decode noRiskLimits.toNat bytes
  if fits_riskLimitsRptGrpComp : riskLimitsRptGrpComp_.length < 256 ^ 1 then
    pure ({ pad2, nrResponseHeaderMeComp, riskLimitReportId, marketSegmentId, partyDetailStatus, riskLimitPlatform, partyDetailExecutingUnit, pad4, riskLimitsRptGrpComp := ⟨riskLimitsRptGrpComp_, fits_riskLimitsRptGrpComp⟩ }, bytes)
  else none

theorem encode_length_pos (message : PreTradeRiskLimitResponse) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : PreTradeRiskLimitResponse) : (encode message).length ≤ 12314 := by
  have bound_riskLimitsRptGrpComp := message.riskLimitsRptGrpComp.length_lt
  unfold encode
  simp only [List.length_append, Alpha.encode_length, NrResponseHeaderMeComp.encode_length, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const RiskLimitsRptGrpComp.encode 48 RiskLimitsRptGrpComp.encode_length]
  omega

@[simp] theorem decode_encode (message : PreTradeRiskLimitResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [NrResponseHeaderMeComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 RiskLimitsRptGrpComp.encode RiskLimitsRptGrpComp.decode RiskLimitsRptGrpComp.decode_encode]
  simp only [Option.bind_some]
  simp only [message.riskLimitsRptGrpComp.length_lt, ↓reduceDIte]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : PreTradeRiskLimitResponse) : decode (encode message) = some (message, []) := by
  have trailing := decode_encode message []
  rw [List.append_nil] at trailing
  exact trailing

end PreTradeRiskLimitResponse

/-- Quote Activation Notification -/
structure QuoteActivationNotification where
  pad2 : Alpha 2
  rbcHeaderMeComp : RbcHeaderMeComp
  massActionReportId : BitVec 64
  marketSegmentId : BitVec 32
  partyIdEnteringTrader : BitVec 32
  partyIdEnteringFirm : BitVec 8
  massActionType : BitVec 8
  massActionSubType : BitVec 8
  massActionReason : BitVec 8
  pad2v2 : Alpha 2
  notAffectedSecuritiesGrpComp : Bounded 2 NotAffectedSecuritiesGrpComp
  deriving DecidableEq, Repr

namespace QuoteActivationNotification

def encode (message : QuoteActivationNotification) : List UInt8 :=
  Alpha.encode message.pad2
    ++ RbcHeaderMeComp.encode message.rbcHeaderMeComp
    ++ encodeUIntLE 8 message.massActionReportId
    ++ encodeUIntLE 4 message.marketSegmentId
    ++ encodeUIntLE 4 message.partyIdEnteringTrader
    ++ encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.notAffectedSecuritiesGrpComp.val.length)
    ++ encodeUInt 1 message.partyIdEnteringFirm
    ++ encodeUInt 1 message.massActionType
    ++ encodeUInt 1 message.massActionSubType
    ++ encodeUInt 1 message.massActionReason
    ++ Alpha.encode message.pad2v2
    ++ encodeMany NotAffectedSecuritiesGrpComp.encode message.notAffectedSecuritiesGrpComp.val

def decode (bytes : List UInt8) : Option (QuoteActivationNotification × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderMeComp, bytes) ← RbcHeaderMeComp.decode bytes
  let (massActionReportId, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (partyIdEnteringTrader, bytes) ← decodeUIntLE 4 bytes
  let (noNotAffectedSecurities, bytes) ← decodeUIntLE 2 bytes
  let (partyIdEnteringFirm, bytes) ← decodeUInt 1 bytes
  let (massActionType, bytes) ← decodeUInt 1 bytes
  let (massActionSubType, bytes) ← decodeUInt 1 bytes
  let (massActionReason, bytes) ← decodeUInt 1 bytes
  let (pad2v2, bytes) ← Alpha.decode 2 bytes
  let (notAffectedSecuritiesGrpComp_, bytes) ← decodeMany NotAffectedSecuritiesGrpComp.decode noNotAffectedSecurities.toNat bytes
  if fits_notAffectedSecuritiesGrpComp : notAffectedSecuritiesGrpComp_.length < 256 ^ 2 then
    pure ({ pad2, rbcHeaderMeComp, massActionReportId, marketSegmentId, partyIdEnteringTrader, partyIdEnteringFirm, massActionType, massActionSubType, massActionReason, pad2v2, notAffectedSecuritiesGrpComp := ⟨notAffectedSecuritiesGrpComp_, fits_notAffectedSecuritiesGrpComp⟩ }, bytes)
  else none

theorem encode_length_pos (message : QuoteActivationNotification) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : QuoteActivationNotification) : (encode message).length ≤ 524362 := by
  have bound_notAffectedSecuritiesGrpComp := message.notAffectedSecuritiesGrpComp.length_lt
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RbcHeaderMeComp.encode_length, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const NotAffectedSecuritiesGrpComp.encode 8 NotAffectedSecuritiesGrpComp.encode_length]
  omega

@[simp] theorem decode_encode (message : QuoteActivationNotification) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [RbcHeaderMeComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 2 NotAffectedSecuritiesGrpComp.encode NotAffectedSecuritiesGrpComp.decode NotAffectedSecuritiesGrpComp.decode_encode]
  simp only [Option.bind_some]
  simp only [message.notAffectedSecuritiesGrpComp.length_lt, ↓reduceDIte]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : QuoteActivationNotification) : decode (encode message) = some (message, []) := by
  have trailing := decode_encode message []
  rw [List.append_nil] at trailing
  exact trailing

end QuoteActivationNotification

/-- Quote Activation Response -/
structure QuoteActivationResponse where
  pad2 : Alpha 2
  nrResponseHeaderMeComp : NrResponseHeaderMeComp
  massActionReportId : BitVec 64
  pad6 : Alpha 6
  notAffectedSecuritiesGrpComp : Bounded 2 NotAffectedSecuritiesGrpComp
  deriving DecidableEq, Repr

namespace QuoteActivationResponse

def encode (message : QuoteActivationResponse) : List UInt8 :=
  Alpha.encode message.pad2
    ++ NrResponseHeaderMeComp.encode message.nrResponseHeaderMeComp
    ++ encodeUIntLE 8 message.massActionReportId
    ++ encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.notAffectedSecuritiesGrpComp.val.length)
    ++ Alpha.encode message.pad6
    ++ encodeMany NotAffectedSecuritiesGrpComp.encode message.notAffectedSecuritiesGrpComp.val

def decode (bytes : List UInt8) : Option (QuoteActivationResponse × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (nrResponseHeaderMeComp, bytes) ← NrResponseHeaderMeComp.decode bytes
  let (massActionReportId, bytes) ← decodeUIntLE 8 bytes
  let (noNotAffectedSecurities, bytes) ← decodeUIntLE 2 bytes
  let (pad6, bytes) ← Alpha.decode 6 bytes
  let (notAffectedSecuritiesGrpComp_, bytes) ← decodeMany NotAffectedSecuritiesGrpComp.decode noNotAffectedSecurities.toNat bytes
  if fits_notAffectedSecuritiesGrpComp : notAffectedSecuritiesGrpComp_.length < 256 ^ 2 then
    pure ({ pad2, nrResponseHeaderMeComp, massActionReportId, pad6, notAffectedSecuritiesGrpComp := ⟨notAffectedSecuritiesGrpComp_, fits_notAffectedSecuritiesGrpComp⟩ }, bytes)
  else none

theorem encode_length_pos (message : QuoteActivationResponse) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : QuoteActivationResponse) : (encode message).length ≤ 524346 := by
  have bound_notAffectedSecuritiesGrpComp := message.notAffectedSecuritiesGrpComp.length_lt
  unfold encode
  simp only [List.length_append, Alpha.encode_length, NrResponseHeaderMeComp.encode_length, encodeUIntLE_length, encodeMany_length_const NotAffectedSecuritiesGrpComp.encode 8 NotAffectedSecuritiesGrpComp.encode_length]
  omega

@[simp] theorem decode_encode (message : QuoteActivationResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [NrResponseHeaderMeComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 2 NotAffectedSecuritiesGrpComp.encode NotAffectedSecuritiesGrpComp.decode NotAffectedSecuritiesGrpComp.decode_encode]
  simp only [Option.bind_some]
  simp only [message.notAffectedSecuritiesGrpComp.length_lt, ↓reduceDIte]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : QuoteActivationResponse) : decode (encode message) = some (message, []) := by
  have trailing := decode_encode message []
  rw [List.append_nil] at trailing
  exact trailing

end QuoteActivationResponse

/-- Quote Event Grp Comp: 48 bytes -/
structure QuoteEventGrpComp where
  securityId : BitVec 64
  quoteEventPx : BitVec 64
  quoteEventQty : BitVec 64
  quoteMsgId : BitVec 64
  quoteEventMatchId : BitVec 32
  quoteEventExecId : BitVec 32
  quoteEventType : BitVec 8
  quoteEventSide : BitVec 8
  quoteEventLiquidityInd : BitVec 8
  quoteEventReason : BitVec 8
  pad4 : Alpha 4
  deriving DecidableEq, Repr

namespace QuoteEventGrpComp

def encode (message : QuoteEventGrpComp) : List UInt8 :=
  encodeUIntLE 8 message.securityId
    ++ encodeUIntLE 8 message.quoteEventPx
    ++ encodeUIntLE 8 message.quoteEventQty
    ++ encodeUIntLE 8 message.quoteMsgId
    ++ encodeUIntLE 4 message.quoteEventMatchId
    ++ encodeUIntLE 4 message.quoteEventExecId
    ++ encodeUInt 1 message.quoteEventType
    ++ encodeUInt 1 message.quoteEventSide
    ++ encodeUInt 1 message.quoteEventLiquidityInd
    ++ encodeUInt 1 message.quoteEventReason
    ++ Alpha.encode message.pad4

def decode (bytes : List UInt8) : Option (QuoteEventGrpComp × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (quoteEventPx, bytes) ← decodeUIntLE 8 bytes
  let (quoteEventQty, bytes) ← decodeUIntLE 8 bytes
  let (quoteMsgId, bytes) ← decodeUIntLE 8 bytes
  let (quoteEventMatchId, bytes) ← decodeUIntLE 4 bytes
  let (quoteEventExecId, bytes) ← decodeUIntLE 4 bytes
  let (quoteEventType, bytes) ← decodeUInt 1 bytes
  let (quoteEventSide, bytes) ← decodeUInt 1 bytes
  let (quoteEventLiquidityInd, bytes) ← decodeUInt 1 bytes
  let (quoteEventReason, bytes) ← decodeUInt 1 bytes
  let (pad4, bytes) ← Alpha.decode 4 bytes
  pure ({ securityId, quoteEventPx, quoteEventQty, quoteMsgId, quoteEventMatchId, quoteEventExecId, quoteEventType, quoteEventSide, quoteEventLiquidityInd, quoteEventReason, pad4 }, bytes)

@[simp] theorem encode_length (message : QuoteEventGrpComp) : (encode message).length = 48 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : QuoteEventGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : QuoteEventGrpComp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end QuoteEventGrpComp

/-- Quote Leg Exec Grp Comp: 32 bytes -/
structure QuoteLegExecGrpComp where
  legSecurityId : BitVec 64
  legLastPx : BitVec 64
  legLastQty : BitVec 64
  legExecId : BitVec 32
  legSide : BitVec 8
  noQuoteEventsIndex : BitVec 8
  pad2 : Alpha 2
  deriving DecidableEq, Repr

namespace QuoteLegExecGrpComp

def encode (message : QuoteLegExecGrpComp) : List UInt8 :=
  encodeUIntLE 8 message.legSecurityId
    ++ encodeUIntLE 8 message.legLastPx
    ++ encodeUIntLE 8 message.legLastQty
    ++ encodeUIntLE 4 message.legExecId
    ++ encodeUInt 1 message.legSide
    ++ encodeUInt 1 message.noQuoteEventsIndex
    ++ Alpha.encode message.pad2

def decode (bytes : List UInt8) : Option (QuoteLegExecGrpComp × List UInt8) := do
  let (legSecurityId, bytes) ← decodeUIntLE 8 bytes
  let (legLastPx, bytes) ← decodeUIntLE 8 bytes
  let (legLastQty, bytes) ← decodeUIntLE 8 bytes
  let (legExecId, bytes) ← decodeUIntLE 4 bytes
  let (legSide, bytes) ← decodeUInt 1 bytes
  let (noQuoteEventsIndex, bytes) ← decodeUInt 1 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  pure ({ legSecurityId, legLastPx, legLastQty, legExecId, legSide, noQuoteEventsIndex, pad2 }, bytes)

@[simp] theorem encode_length (message : QuoteLegExecGrpComp) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : QuoteLegExecGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : QuoteLegExecGrpComp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end QuoteLegExecGrpComp

/-- Quote Execution Report -/
structure QuoteExecutionReport where
  pad2 : Alpha 2
  rbcHeaderMeComp : RbcHeaderMeComp
  execId : BitVec 64
  marketSegmentId : BitVec 32
  pad1 : Alpha 1
  quoteEventGrpComp : Bounded 1 QuoteEventGrpComp
  quoteLegExecGrpComp : Bounded 2 QuoteLegExecGrpComp
  deriving DecidableEq, Repr

namespace QuoteExecutionReport

def encode (message : QuoteExecutionReport) : List UInt8 :=
  Alpha.encode message.pad2
    ++ RbcHeaderMeComp.encode message.rbcHeaderMeComp
    ++ encodeUIntLE 8 message.execId
    ++ encodeUIntLE 4 message.marketSegmentId
    ++ encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.quoteLegExecGrpComp.val.length)
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.quoteEventGrpComp.val.length)
    ++ Alpha.encode message.pad1
    ++ encodeMany QuoteEventGrpComp.encode message.quoteEventGrpComp.val
    ++ encodeMany QuoteLegExecGrpComp.encode message.quoteLegExecGrpComp.val

def decode (bytes : List UInt8) : Option (QuoteExecutionReport × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderMeComp, bytes) ← RbcHeaderMeComp.decode bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (noLegExecs, bytes) ← decodeUIntLE 2 bytes
  let (noQuoteEvents, bytes) ← decodeUInt 1 bytes
  let (pad1, bytes) ← Alpha.decode 1 bytes
  let (quoteEventGrpComp_, bytes) ← decodeMany QuoteEventGrpComp.decode noQuoteEvents.toNat bytes
  let (quoteLegExecGrpComp_, bytes) ← decodeMany QuoteLegExecGrpComp.decode noLegExecs.toNat bytes
  if fits_quoteEventGrpComp : quoteEventGrpComp_.length < 256 ^ 1 then
    if fits_quoteLegExecGrpComp : quoteLegExecGrpComp_.length < 256 ^ 2 then
      pure ({ pad2, rbcHeaderMeComp, execId, marketSegmentId, pad1, quoteEventGrpComp := ⟨quoteEventGrpComp_, fits_quoteEventGrpComp⟩, quoteLegExecGrpComp := ⟨quoteLegExecGrpComp_, fits_quoteLegExecGrpComp⟩ }, bytes)
    else none
  else none

theorem encode_length_pos (message : QuoteExecutionReport) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : QuoteExecutionReport) : (encode message).length ≤ 2109434 := by
  have bound_quoteEventGrpComp := message.quoteEventGrpComp.length_lt
  have bound_quoteLegExecGrpComp := message.quoteLegExecGrpComp.length_lt
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RbcHeaderMeComp.encode_length, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const QuoteEventGrpComp.encode 48 QuoteEventGrpComp.encode_length, encodeMany_length_const QuoteLegExecGrpComp.encode 32 QuoteLegExecGrpComp.encode_length]
  omega

@[simp] theorem decode_encode (message : QuoteExecutionReport) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [RbcHeaderMeComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 QuoteEventGrpComp.encode QuoteEventGrpComp.decode QuoteEventGrpComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 2 QuoteLegExecGrpComp.encode QuoteLegExecGrpComp.decode QuoteLegExecGrpComp.decode_encode]
  simp only [Option.bind_some]
  simp only [message.quoteEventGrpComp.length_lt, message.quoteLegExecGrpComp.length_lt, ↓reduceDIte]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : QuoteExecutionReport) : decode (encode message) = some (message, []) := by
  have trailing := decode_encode message []
  rw [List.append_nil] at trailing
  exact trailing

end QuoteExecutionReport

/-- Rfq Response: 58 bytes -/
structure RfqResponse where
  pad2 : Alpha 2
  nrResponseHeaderMeComp : NrResponseHeaderMeComp
  execId : BitVec 64
  deriving DecidableEq, Repr

namespace RfqResponse

def encode (message : RfqResponse) : List UInt8 :=
  Alpha.encode message.pad2
    ++ NrResponseHeaderMeComp.encode message.nrResponseHeaderMeComp
    ++ encodeUIntLE 8 message.execId

def decode (bytes : List UInt8) : Option (RfqResponse × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (nrResponseHeaderMeComp, bytes) ← NrResponseHeaderMeComp.decode bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  pure ({ pad2, nrResponseHeaderMeComp, execId }, bytes)

@[simp] theorem encode_length (message : RfqResponse) : (encode message).length = 58 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, NrResponseHeaderMeComp.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : RfqResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RfqResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [NrResponseHeaderMeComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : RfqResponse) : decode (encode message) = some (message, []) := by
  have trailing := decode_encode message []
  rw [List.append_nil] at trailing
  exact trailing

end RfqResponse

/-- Reject -/
structure Reject where
  pad2 : Alpha 2
  nrResponseHeaderMeComp : NrResponseHeaderMeComp
  sessionRejectReason : BitVec 32
  sessionStatus : BitVec 8
  varText : Bounded 2 UInt8
  alignmentPadding : Capped 4282374239
  deriving DecidableEq, Repr

namespace Reject

def encode (message : Reject) : List UInt8 :=
  Alpha.encode message.pad2
    ++ NrResponseHeaderMeComp.encode message.nrResponseHeaderMeComp
    ++ encodeUIntLE 4 message.sessionRejectReason
    ++ encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.varText.val.length)
    ++ encodeUInt 1 message.sessionStatus
    ++ encodeMany Byte.encode message.varText.val
    ++ message.alignmentPadding.val

def decode (bytes : List UInt8) : Option Reject := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (nrResponseHeaderMeComp, bytes) ← NrResponseHeaderMeComp.decode bytes
  let (sessionRejectReason, bytes) ← decodeUIntLE 4 bytes
  let (varTextLen, bytes) ← decodeUIntLE 2 bytes
  let (sessionStatus, bytes) ← decodeUInt 1 bytes
  let (varText_, bytes) ← decodeMany Byte.decode varTextLen.toNat bytes
  let alignmentPadding_ := bytes
  if fits_varText : varText_.length < 256 ^ 2 then
    if fits_alignmentPadding : alignmentPadding_.length ≤ 4282374239 then
      pure { pad2, nrResponseHeaderMeComp, sessionRejectReason, sessionStatus, varText := ⟨varText_, fits_varText⟩, alignmentPadding := ⟨alignmentPadding_, fits_alignmentPadding⟩ }
    else none
  else none

theorem encode_length_pos (message : Reject) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : Reject) : (encode message).length ≤ 4282439831 := by
  have bound_varText := message.varText.length_lt
  have bound_alignmentPadding := message.alignmentPadding.length_le
  unfold encode
  simp only [List.length_append, Alpha.encode_length, NrResponseHeaderMeComp.encode_length, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const Byte.encode 1 Byte.encode_length]
  omega

theorem decode_encode (message : Reject) : decode (encode message) = some message := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [NrResponseHeaderMeComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 2 Byte.encode Byte.decode Byte.decode_encode]
  simp only [Option.bind_some]
  simp only [message.varText.length_lt, message.alignmentPadding.length_le, ↓reduceDIte]
  rfl

end Reject

/-- Retransmit Me Message Response: 66 bytes -/
structure RetransmitMeMessageResponse where
  pad2 : Alpha 2
  responseHeaderComp : ResponseHeaderComp
  applTotalMessageCount : BitVec 16
  applEndMsgId : Alpha 16
  refApplLastMsgId : Alpha 16
  pad6 : Alpha 6
  deriving DecidableEq, Repr

namespace RetransmitMeMessageResponse

def encode (message : RetransmitMeMessageResponse) : List UInt8 :=
  Alpha.encode message.pad2
    ++ ResponseHeaderComp.encode message.responseHeaderComp
    ++ encodeUIntLE 2 message.applTotalMessageCount
    ++ Alpha.encode message.applEndMsgId
    ++ Alpha.encode message.refApplLastMsgId
    ++ Alpha.encode message.pad6

def decode (bytes : List UInt8) : Option (RetransmitMeMessageResponse × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (responseHeaderComp, bytes) ← ResponseHeaderComp.decode bytes
  let (applTotalMessageCount, bytes) ← decodeUIntLE 2 bytes
  let (applEndMsgId, bytes) ← Alpha.decode 16 bytes
  let (refApplLastMsgId, bytes) ← Alpha.decode 16 bytes
  let (pad6, bytes) ← Alpha.decode 6 bytes
  pure ({ pad2, responseHeaderComp, applTotalMessageCount, applEndMsgId, refApplLastMsgId, pad6 }, bytes)

@[simp] theorem encode_length (message : RetransmitMeMessageResponse) : (encode message).length = 66 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, ResponseHeaderComp.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : RetransmitMeMessageResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RetransmitMeMessageResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [ResponseHeaderComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : RetransmitMeMessageResponse) : decode (encode message) = some (message, []) := by
  have trailing := decode_encode message []
  rw [List.append_nil] at trailing
  exact trailing

end RetransmitMeMessageResponse

/-- Retransmit Response: 50 bytes -/
structure RetransmitResponse where
  pad2 : Alpha 2
  responseHeaderComp : ResponseHeaderComp
  applEndSeqNum : BitVec 64
  refApplLastSeqNum : BitVec 64
  applTotalMessageCount : BitVec 16
  pad6 : Alpha 6
  deriving DecidableEq, Repr

namespace RetransmitResponse

def encode (message : RetransmitResponse) : List UInt8 :=
  Alpha.encode message.pad2
    ++ ResponseHeaderComp.encode message.responseHeaderComp
    ++ encodeUIntLE 8 message.applEndSeqNum
    ++ encodeUIntLE 8 message.refApplLastSeqNum
    ++ encodeUIntLE 2 message.applTotalMessageCount
    ++ Alpha.encode message.pad6

def decode (bytes : List UInt8) : Option (RetransmitResponse × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (responseHeaderComp, bytes) ← ResponseHeaderComp.decode bytes
  let (applEndSeqNum, bytes) ← decodeUIntLE 8 bytes
  let (refApplLastSeqNum, bytes) ← decodeUIntLE 8 bytes
  let (applTotalMessageCount, bytes) ← decodeUIntLE 2 bytes
  let (pad6, bytes) ← Alpha.decode 6 bytes
  pure ({ pad2, responseHeaderComp, applEndSeqNum, refApplLastSeqNum, applTotalMessageCount, pad6 }, bytes)

@[simp] theorem encode_length (message : RetransmitResponse) : (encode message).length = 50 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, ResponseHeaderComp.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : RetransmitResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RetransmitResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [ResponseHeaderComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : RetransmitResponse) : decode (encode message) = some (message, []) := by
  have trailing := decode_encode message []
  rw [List.append_nil] at trailing
  exact trailing

end RetransmitResponse

/-- Risk Notification Broadcast: 82 bytes -/
structure RiskNotificationBroadcast where
  pad2 : Alpha 2
  rbcHeaderComp : RbcHeaderComp
  transactTime : BitVec 64
  tradeDate : BitVec 32
  partyDetailIdExecutingUnit : BitVec 32
  requestingPartyIdExecutingSystem : BitVec 32
  marketId : BitVec 16
  inventoryCheckType : BitVec 8
  listUpdateAction : ListUpdateAction
  riskLimitAction : BitVec 8
  requestingPartyEnteringFirm : Alpha 9
  requestingPartyClearingFirm : Alpha 9
  pad5 : Alpha 5
  deriving DecidableEq, Repr

namespace RiskNotificationBroadcast

def encode (message : RiskNotificationBroadcast) : List UInt8 :=
  Alpha.encode message.pad2
    ++ RbcHeaderComp.encode message.rbcHeaderComp
    ++ encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 4 message.tradeDate
    ++ encodeUIntLE 4 message.partyDetailIdExecutingUnit
    ++ encodeUIntLE 4 message.requestingPartyIdExecutingSystem
    ++ encodeUIntLE 2 message.marketId
    ++ encodeUInt 1 message.inventoryCheckType
    ++ ListUpdateAction.encode message.listUpdateAction
    ++ encodeUInt 1 message.riskLimitAction
    ++ Alpha.encode message.requestingPartyEnteringFirm
    ++ Alpha.encode message.requestingPartyClearingFirm
    ++ Alpha.encode message.pad5

def decode (bytes : List UInt8) : Option (RiskNotificationBroadcast × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderComp, bytes) ← RbcHeaderComp.decode bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (tradeDate, bytes) ← decodeUIntLE 4 bytes
  let (partyDetailIdExecutingUnit, bytes) ← decodeUIntLE 4 bytes
  let (requestingPartyIdExecutingSystem, bytes) ← decodeUIntLE 4 bytes
  let (marketId, bytes) ← decodeUIntLE 2 bytes
  let (inventoryCheckType, bytes) ← decodeUInt 1 bytes
  let (listUpdateAction, bytes) ← ListUpdateAction.decode bytes
  let (riskLimitAction, bytes) ← decodeUInt 1 bytes
  let (requestingPartyEnteringFirm, bytes) ← Alpha.decode 9 bytes
  let (requestingPartyClearingFirm, bytes) ← Alpha.decode 9 bytes
  let (pad5, bytes) ← Alpha.decode 5 bytes
  pure ({ pad2, rbcHeaderComp, transactTime, tradeDate, partyDetailIdExecutingUnit, requestingPartyIdExecutingSystem, marketId, inventoryCheckType, listUpdateAction, riskLimitAction, requestingPartyEnteringFirm, requestingPartyClearingFirm, pad5 }, bytes)

@[simp] theorem encode_length (message : RiskNotificationBroadcast) : (encode message).length = 82 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RbcHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length, ListUpdateAction.encode_length]

theorem encode_length_pos (message : RiskNotificationBroadcast) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RiskNotificationBroadcast) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [RbcHeaderComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [ListUpdateAction.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : RiskNotificationBroadcast) : decode (encode message) = some (message, []) := by
  have trailing := decode_encode message []
  rw [List.append_nil] at trailing
  exact trailing

end RiskNotificationBroadcast

/-- Order Book Item Grp Comp: 48 bytes -/
structure OrderBookItemGrpComp where
  securityId : BitVec 64
  bestBidPx : BitVec 64
  bestBidSize : BitVec 64
  bestOfferPx : BitVec 64
  bestOfferSize : BitVec 64
  mdBookType : BitVec 8
  mdSubBookType : BitVec 8
  pad6 : Alpha 6
  deriving DecidableEq, Repr

namespace OrderBookItemGrpComp

def encode (message : OrderBookItemGrpComp) : List UInt8 :=
  encodeUIntLE 8 message.securityId
    ++ encodeUIntLE 8 message.bestBidPx
    ++ encodeUIntLE 8 message.bestBidSize
    ++ encodeUIntLE 8 message.bestOfferPx
    ++ encodeUIntLE 8 message.bestOfferSize
    ++ encodeUInt 1 message.mdBookType
    ++ encodeUInt 1 message.mdSubBookType
    ++ Alpha.encode message.pad6

def decode (bytes : List UInt8) : Option (OrderBookItemGrpComp × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (bestBidPx, bytes) ← decodeUIntLE 8 bytes
  let (bestBidSize, bytes) ← decodeUIntLE 8 bytes
  let (bestOfferPx, bytes) ← decodeUIntLE 8 bytes
  let (bestOfferSize, bytes) ← decodeUIntLE 8 bytes
  let (mdBookType, bytes) ← decodeUInt 1 bytes
  let (mdSubBookType, bytes) ← decodeUInt 1 bytes
  let (pad6, bytes) ← Alpha.decode 6 bytes
  pure ({ securityId, bestBidPx, bestBidSize, bestOfferPx, bestOfferSize, mdBookType, mdSubBookType, pad6 }, bytes)

@[simp] theorem encode_length (message : OrderBookItemGrpComp) : (encode message).length = 48 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : OrderBookItemGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderBookItemGrpComp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end OrderBookItemGrpComp

/-- Srqs Target Party Trd Grp Comp: 40 bytes -/
structure SrqsTargetPartyTrdGrpComp where
  sideLastQty : BitVec 64
  quoteId : BitVec 64
  targetPartyIdExecutingTrader : BitVec 32
  targetPartyExecutingFirm : Alpha 5
  targetPartyExecutingTrader : Alpha 6
  targetPartyEnteringTrader : Alpha 6
  pad3 : Alpha 3
  deriving DecidableEq, Repr

namespace SrqsTargetPartyTrdGrpComp

def encode (message : SrqsTargetPartyTrdGrpComp) : List UInt8 :=
  encodeUIntLE 8 message.sideLastQty
    ++ encodeUIntLE 8 message.quoteId
    ++ encodeUIntLE 4 message.targetPartyIdExecutingTrader
    ++ Alpha.encode message.targetPartyExecutingFirm
    ++ Alpha.encode message.targetPartyExecutingTrader
    ++ Alpha.encode message.targetPartyEnteringTrader
    ++ Alpha.encode message.pad3

def decode (bytes : List UInt8) : Option (SrqsTargetPartyTrdGrpComp × List UInt8) := do
  let (sideLastQty, bytes) ← decodeUIntLE 8 bytes
  let (quoteId, bytes) ← decodeUIntLE 8 bytes
  let (targetPartyIdExecutingTrader, bytes) ← decodeUIntLE 4 bytes
  let (targetPartyExecutingFirm, bytes) ← Alpha.decode 5 bytes
  let (targetPartyExecutingTrader, bytes) ← Alpha.decode 6 bytes
  let (targetPartyEnteringTrader, bytes) ← Alpha.decode 6 bytes
  let (pad3, bytes) ← Alpha.decode 3 bytes
  pure ({ sideLastQty, quoteId, targetPartyIdExecutingTrader, targetPartyExecutingFirm, targetPartyExecutingTrader, targetPartyEnteringTrader, pad3 }, bytes)

@[simp] theorem encode_length (message : SrqsTargetPartyTrdGrpComp) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : SrqsTargetPartyTrdGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SrqsTargetPartyTrdGrpComp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end SrqsTargetPartyTrdGrpComp

/-- Srqs Create Deal Notification -/
structure SrqsCreateDealNotification where
  pad2 : Alpha 2
  rbcHeaderComp : RbcHeaderComp
  transactTime : BitVec 64
  lastPx : BitVec 64
  lastQty : BitVec 64
  securityId : BitVec 64
  expireTime : BitVec 64
  underlyingPx : BitVec 64
  underlyingDeltaPercentage : BitVec 64
  underlyingEffectiveDeltaPercentage : BitVec 64
  underlyingQty : BitVec 64
  underlyingPriceStipValue : BitVec 64
  negotiationId : BitVec 32
  tradeId : BitVec 32
  origTradeId : BitVec 32
  trdRptStatus : BitVec 8
  tradeReportType : BitVec 8
  messageEventSource : MessageEventSource
  side : BitVec 8
  tradingCapacity : BitVec 8
  tradePublishIndicator : BitVec 8
  hedgingInstruction : BitVec 8
  rootPartyExecutingFirm : Alpha 5
  rootPartyExecutingTrader : Alpha 6
  rootPartyEnteringTrader : Alpha 6
  firmTradeId : Alpha 20
  firmNegotiationId : Alpha 20
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
  pad3 : Alpha 3
  orderBookItemGrpComp : Bounded 1 OrderBookItemGrpComp
  srqsTargetPartyTrdGrpComp : Bounded 1 SrqsTargetPartyTrdGrpComp
  deriving DecidableEq, Repr

namespace SrqsCreateDealNotification

def encode (message : SrqsCreateDealNotification) : List UInt8 :=
  Alpha.encode message.pad2
    ++ RbcHeaderComp.encode message.rbcHeaderComp
    ++ encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 8 message.lastPx
    ++ encodeUIntLE 8 message.lastQty
    ++ encodeUIntLE 8 message.securityId
    ++ encodeUIntLE 8 message.expireTime
    ++ encodeUIntLE 8 message.underlyingPx
    ++ encodeUIntLE 8 message.underlyingDeltaPercentage
    ++ encodeUIntLE 8 message.underlyingEffectiveDeltaPercentage
    ++ encodeUIntLE 8 message.underlyingQty
    ++ encodeUIntLE 8 message.underlyingPriceStipValue
    ++ encodeUIntLE 4 message.negotiationId
    ++ encodeUIntLE 4 message.tradeId
    ++ encodeUIntLE 4 message.origTradeId
    ++ encodeUInt 1 message.trdRptStatus
    ++ encodeUInt 1 message.tradeReportType
    ++ MessageEventSource.encode message.messageEventSource
    ++ encodeUInt 1 message.side
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.orderBookItemGrpComp.val.length)
    ++ encodeUInt 1 message.tradingCapacity
    ++ encodeUInt 1 message.tradePublishIndicator
    ++ encodeUInt 1 message.hedgingInstruction
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.srqsTargetPartyTrdGrpComp.val.length)
    ++ Alpha.encode message.rootPartyExecutingFirm
    ++ Alpha.encode message.rootPartyExecutingTrader
    ++ Alpha.encode message.rootPartyEnteringTrader
    ++ Alpha.encode message.firmTradeId
    ++ Alpha.encode message.firmNegotiationId
    ++ Alpha.encode message.freeText1
    ++ Alpha.encode message.freeText2
    ++ Alpha.encode message.freeText3
    ++ Alpha.encode message.freeText5
    ++ PositionEffect.encode message.positionEffect
    ++ Alpha.encode message.account
    ++ Alpha.encode message.partyIdBeneficiary
    ++ CustOrderHandlingInst.encode message.custOrderHandlingInst
    ++ Alpha.encode message.partyIdOrderOriginationFirm
    ++ Alpha.encode message.partyIdPositionAccount
    ++ Alpha.encode message.partyIdLocationId
    ++ Alpha.encode message.complianceText
    ++ Alpha.encode message.partyIdTakeUpTradingFirm
    ++ Alpha.encode message.pad3
    ++ encodeMany OrderBookItemGrpComp.encode message.orderBookItemGrpComp.val
    ++ encodeMany SrqsTargetPartyTrdGrpComp.encode message.srqsTargetPartyTrdGrpComp.val

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (SrqsCreateDealNotification × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderComp, bytes) ← RbcHeaderComp.decode bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  let (lastQty, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (expireTime, bytes) ← decodeUIntLE 8 bytes
  let (underlyingPx, bytes) ← decodeUIntLE 8 bytes
  let (underlyingDeltaPercentage, bytes) ← decodeUIntLE 8 bytes
  let (underlyingEffectiveDeltaPercentage, bytes) ← decodeUIntLE 8 bytes
  let (underlyingQty, bytes) ← decodeUIntLE 8 bytes
  let (underlyingPriceStipValue, bytes) ← decodeUIntLE 8 bytes
  let (negotiationId, bytes) ← decodeUIntLE 4 bytes
  let (tradeId, bytes) ← decodeUIntLE 4 bytes
  let (origTradeId, bytes) ← decodeUIntLE 4 bytes
  let (trdRptStatus, bytes) ← decodeUInt 1 bytes
  let (tradeReportType, bytes) ← decodeUInt 1 bytes
  let (messageEventSource, bytes) ← MessageEventSource.decode bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (noOrderBookItems, bytes) ← decodeUInt 1 bytes
  let (tradingCapacity, bytes) ← decodeUInt 1 bytes
  let (tradePublishIndicator, bytes) ← decodeUInt 1 bytes
  let (hedgingInstruction, bytes) ← decodeUInt 1 bytes
  let (noSrqsTargetPartyTrdGrps, bytes) ← decodeUInt 1 bytes
  let (rootPartyExecutingFirm, bytes) ← Alpha.decode 5 bytes
  let (rootPartyExecutingTrader, bytes) ← Alpha.decode 6 bytes
  let (rootPartyEnteringTrader, bytes) ← Alpha.decode 6 bytes
  let (firmTradeId, bytes) ← Alpha.decode 20 bytes
  let (firmNegotiationId, bytes) ← Alpha.decode 20 bytes
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
  let (pad3, bytes) ← Alpha.decode 3 bytes
  let (orderBookItemGrpComp_, bytes) ← decodeMany OrderBookItemGrpComp.decode noOrderBookItems.toNat bytes
  let (srqsTargetPartyTrdGrpComp_, bytes) ← decodeMany SrqsTargetPartyTrdGrpComp.decode noSrqsTargetPartyTrdGrps.toNat bytes
  if fits_orderBookItemGrpComp : orderBookItemGrpComp_.length < 256 ^ 1 then
    if fits_srqsTargetPartyTrdGrpComp : srqsTargetPartyTrdGrpComp_.length < 256 ^ 1 then
      pure ({ pad2, rbcHeaderComp, transactTime, lastPx, lastQty, securityId, expireTime, underlyingPx, underlyingDeltaPercentage, underlyingEffectiveDeltaPercentage, underlyingQty, underlyingPriceStipValue, negotiationId, tradeId, origTradeId, trdRptStatus, tradeReportType, messageEventSource, side, tradingCapacity, tradePublishIndicator, hedgingInstruction, rootPartyExecutingFirm, rootPartyExecutingTrader, rootPartyEnteringTrader, firmTradeId, firmNegotiationId, freeText1, freeText2, freeText3, freeText5, positionEffect, account, partyIdBeneficiary, custOrderHandlingInst, partyIdOrderOriginationFirm, partyIdPositionAccount, partyIdLocationId, complianceText, partyIdTakeUpTradingFirm, pad3, orderBookItemGrpComp := ⟨orderBookItemGrpComp_, fits_orderBookItemGrpComp⟩, srqsTargetPartyTrdGrpComp := ⟨srqsTargetPartyTrdGrpComp_, fits_srqsTargetPartyTrdGrpComp⟩ }, bytes)
    else none
  else none

theorem encode_length_pos (message : SrqsCreateDealNotification) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SrqsCreateDealNotification) : (encode message).length ≤ 22882 := by
  have bound_orderBookItemGrpComp := message.orderBookItemGrpComp.length_lt
  have bound_srqsTargetPartyTrdGrpComp := message.srqsTargetPartyTrdGrpComp.length_lt
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RbcHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length, MessageEventSource.encode_length, PositionEffect.encode_length, CustOrderHandlingInst.encode_length, encodeMany_length_const OrderBookItemGrpComp.encode 48 OrderBookItemGrpComp.encode_length, encodeMany_length_const SrqsTargetPartyTrdGrpComp.encode 40 SrqsTargetPartyTrdGrpComp.encode_length]
  omega

@[simp] theorem decode_encode (message : SrqsCreateDealNotification) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [RbcHeaderComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [MessageEventSource.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [PositionEffect.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [CustOrderHandlingInst.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 OrderBookItemGrpComp.encode OrderBookItemGrpComp.decode OrderBookItemGrpComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 SrqsTargetPartyTrdGrpComp.encode SrqsTargetPartyTrdGrpComp.decode SrqsTargetPartyTrdGrpComp.decode_encode]
  simp only [Option.bind_some]
  simp only [message.orderBookItemGrpComp.length_lt, message.srqsTargetPartyTrdGrpComp.length_lt, ↓reduceDIte]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : SrqsCreateDealNotification) : decode (encode message) = some (message, []) := by
  have trailing := decode_encode message []
  rw [List.append_nil] at trailing
  exact trailing

end SrqsCreateDealNotification

/-- Srqs Deal Notification -/
structure SrqsDealNotification where
  pad2 : Alpha 2
  rbcHeaderComp : RbcHeaderComp
  transactTime : BitVec 64
  underlyingPriceStipValue : BitVec 64
  underlyingPx : BitVec 64
  lastPx : BitVec 64
  lastQty : BitVec 64
  negotiationId : BitVec 32
  tradeId : BitVec 32
  requestingPartySubIdType : BitVec 16
  trdRptStatus : BitVec 8
  tradeRequestResult : BitVec 8
  messageEventSource : MessageEventSource
  tradingCapacity : BitVec 8
  rootPartyExecutingFirm : Alpha 5
  rootPartyExecutingTrader : Alpha 6
  rootPartyEnteringTrader : Alpha 6
  firmTradeId : Alpha 20
  firmNegotiationId : Alpha 20
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
  pad1 : Alpha 1
  srqsTargetPartyTrdGrpComp : Bounded 1 SrqsTargetPartyTrdGrpComp
  deriving DecidableEq, Repr

namespace SrqsDealNotification

def encode (message : SrqsDealNotification) : List UInt8 :=
  Alpha.encode message.pad2
    ++ RbcHeaderComp.encode message.rbcHeaderComp
    ++ encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 8 message.underlyingPriceStipValue
    ++ encodeUIntLE 8 message.underlyingPx
    ++ encodeUIntLE 8 message.lastPx
    ++ encodeUIntLE 8 message.lastQty
    ++ encodeUIntLE 4 message.negotiationId
    ++ encodeUIntLE 4 message.tradeId
    ++ encodeUIntLE 2 message.requestingPartySubIdType
    ++ encodeUInt 1 message.trdRptStatus
    ++ encodeUInt 1 message.tradeRequestResult
    ++ MessageEventSource.encode message.messageEventSource
    ++ encodeUInt 1 message.tradingCapacity
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.srqsTargetPartyTrdGrpComp.val.length)
    ++ Alpha.encode message.rootPartyExecutingFirm
    ++ Alpha.encode message.rootPartyExecutingTrader
    ++ Alpha.encode message.rootPartyEnteringTrader
    ++ Alpha.encode message.firmTradeId
    ++ Alpha.encode message.firmNegotiationId
    ++ Alpha.encode message.freeText1
    ++ Alpha.encode message.freeText2
    ++ Alpha.encode message.freeText3
    ++ Alpha.encode message.freeText5
    ++ PositionEffect.encode message.positionEffect
    ++ Alpha.encode message.account
    ++ Alpha.encode message.partyIdBeneficiary
    ++ CustOrderHandlingInst.encode message.custOrderHandlingInst
    ++ Alpha.encode message.partyIdOrderOriginationFirm
    ++ Alpha.encode message.partyIdPositionAccount
    ++ Alpha.encode message.partyIdLocationId
    ++ Alpha.encode message.complianceText
    ++ Alpha.encode message.partyIdTakeUpTradingFirm
    ++ Alpha.encode message.pad1
    ++ encodeMany SrqsTargetPartyTrdGrpComp.encode message.srqsTargetPartyTrdGrpComp.val

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (SrqsDealNotification × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderComp, bytes) ← RbcHeaderComp.decode bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (underlyingPriceStipValue, bytes) ← decodeUIntLE 8 bytes
  let (underlyingPx, bytes) ← decodeUIntLE 8 bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  let (lastQty, bytes) ← decodeUIntLE 8 bytes
  let (negotiationId, bytes) ← decodeUIntLE 4 bytes
  let (tradeId, bytes) ← decodeUIntLE 4 bytes
  let (requestingPartySubIdType, bytes) ← decodeUIntLE 2 bytes
  let (trdRptStatus, bytes) ← decodeUInt 1 bytes
  let (tradeRequestResult, bytes) ← decodeUInt 1 bytes
  let (messageEventSource, bytes) ← MessageEventSource.decode bytes
  let (tradingCapacity, bytes) ← decodeUInt 1 bytes
  let (noSrqsTargetPartyTrdGrps, bytes) ← decodeUInt 1 bytes
  let (rootPartyExecutingFirm, bytes) ← Alpha.decode 5 bytes
  let (rootPartyExecutingTrader, bytes) ← Alpha.decode 6 bytes
  let (rootPartyEnteringTrader, bytes) ← Alpha.decode 6 bytes
  let (firmTradeId, bytes) ← Alpha.decode 20 bytes
  let (firmNegotiationId, bytes) ← Alpha.decode 20 bytes
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
  let (pad1, bytes) ← Alpha.decode 1 bytes
  let (srqsTargetPartyTrdGrpComp_, bytes) ← decodeMany SrqsTargetPartyTrdGrpComp.decode noSrqsTargetPartyTrdGrps.toNat bytes
  if fits_srqsTargetPartyTrdGrpComp : srqsTargetPartyTrdGrpComp_.length < 256 ^ 1 then
    pure ({ pad2, rbcHeaderComp, transactTime, underlyingPriceStipValue, underlyingPx, lastPx, lastQty, negotiationId, tradeId, requestingPartySubIdType, trdRptStatus, tradeRequestResult, messageEventSource, tradingCapacity, rootPartyExecutingFirm, rootPartyExecutingTrader, rootPartyEnteringTrader, firmTradeId, firmNegotiationId, freeText1, freeText2, freeText3, freeText5, positionEffect, account, partyIdBeneficiary, custOrderHandlingInst, partyIdOrderOriginationFirm, partyIdPositionAccount, partyIdLocationId, complianceText, partyIdTakeUpTradingFirm, pad1, srqsTargetPartyTrdGrpComp := ⟨srqsTargetPartyTrdGrpComp_, fits_srqsTargetPartyTrdGrpComp⟩ }, bytes)
  else none

theorem encode_length_pos (message : SrqsDealNotification) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SrqsDealNotification) : (encode message).length ≤ 10594 := by
  have bound_srqsTargetPartyTrdGrpComp := message.srqsTargetPartyTrdGrpComp.length_lt
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RbcHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length, MessageEventSource.encode_length, PositionEffect.encode_length, CustOrderHandlingInst.encode_length, encodeMany_length_const SrqsTargetPartyTrdGrpComp.encode 40 SrqsTargetPartyTrdGrpComp.encode_length]
  omega

@[simp] theorem decode_encode (message : SrqsDealNotification) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [RbcHeaderComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [MessageEventSource.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [PositionEffect.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [CustOrderHandlingInst.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 SrqsTargetPartyTrdGrpComp.encode SrqsTargetPartyTrdGrpComp.decode SrqsTargetPartyTrdGrpComp.decode_encode]
  simp only [Option.bind_some]
  simp only [message.srqsTargetPartyTrdGrpComp.length_lt, ↓reduceDIte]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : SrqsDealNotification) : decode (encode message) = some (message, []) := by
  have trailing := decode_encode message []
  rw [List.append_nil] at trailing
  exact trailing

end SrqsDealNotification

/-- Srqs Quote Grp Comp: 8 bytes -/
structure SrqsQuoteGrpComp where
  quoteId : BitVec 64
  deriving DecidableEq, Repr

namespace SrqsQuoteGrpComp

def encode (message : SrqsQuoteGrpComp) : List UInt8 :=
  encodeUIntLE 8 message.quoteId

def decode (bytes : List UInt8) : Option (SrqsQuoteGrpComp × List UInt8) := do
  let (quoteId, bytes) ← decodeUIntLE 8 bytes
  pure ({ quoteId }, bytes)

@[simp] theorem encode_length (message : SrqsQuoteGrpComp) : (encode message).length = 8 := by
  unfold encode
  simp only [encodeUIntLE_length]

theorem encode_length_pos (message : SrqsQuoteGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SrqsQuoteGrpComp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

end SrqsQuoteGrpComp

/-- Srqs Deal Response -/
structure SrqsDealResponse where
  pad2 : Alpha 2
  responseHeaderComp : ResponseHeaderComp
  securityId : BitVec 64
  negotiationId : BitVec 32
  tradeId : BitVec 32
  secondaryTradeId : BitVec 32
  firmTradeId : Alpha 20
  firmNegotiationId : Alpha 20
  pad3 : Alpha 3
  srqsQuoteGrpComp : Bounded 1 SrqsQuoteGrpComp
  deriving DecidableEq, Repr

namespace SrqsDealResponse

def encode (message : SrqsDealResponse) : List UInt8 :=
  Alpha.encode message.pad2
    ++ ResponseHeaderComp.encode message.responseHeaderComp
    ++ encodeUIntLE 8 message.securityId
    ++ encodeUIntLE 4 message.negotiationId
    ++ encodeUIntLE 4 message.tradeId
    ++ encodeUIntLE 4 message.secondaryTradeId
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.srqsQuoteGrpComp.val.length)
    ++ Alpha.encode message.firmTradeId
    ++ Alpha.encode message.firmNegotiationId
    ++ Alpha.encode message.pad3
    ++ encodeMany SrqsQuoteGrpComp.encode message.srqsQuoteGrpComp.val

def decode (bytes : List UInt8) : Option (SrqsDealResponse × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (responseHeaderComp, bytes) ← ResponseHeaderComp.decode bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (negotiationId, bytes) ← decodeUIntLE 4 bytes
  let (tradeId, bytes) ← decodeUIntLE 4 bytes
  let (secondaryTradeId, bytes) ← decodeUIntLE 4 bytes
  let (noSrqsQuoteGrps, bytes) ← decodeUInt 1 bytes
  let (firmTradeId, bytes) ← Alpha.decode 20 bytes
  let (firmNegotiationId, bytes) ← Alpha.decode 20 bytes
  let (pad3, bytes) ← Alpha.decode 3 bytes
  let (srqsQuoteGrpComp_, bytes) ← decodeMany SrqsQuoteGrpComp.decode noSrqsQuoteGrps.toNat bytes
  if fits_srqsQuoteGrpComp : srqsQuoteGrpComp_.length < 256 ^ 1 then
    pure ({ pad2, responseHeaderComp, securityId, negotiationId, tradeId, secondaryTradeId, firmTradeId, firmNegotiationId, pad3, srqsQuoteGrpComp := ⟨srqsQuoteGrpComp_, fits_srqsQuoteGrpComp⟩ }, bytes)
  else none

theorem encode_length_pos (message : SrqsDealResponse) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SrqsDealResponse) : (encode message).length ≤ 2130 := by
  have bound_srqsQuoteGrpComp := message.srqsQuoteGrpComp.length_lt
  unfold encode
  simp only [List.length_append, Alpha.encode_length, ResponseHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const SrqsQuoteGrpComp.encode 8 SrqsQuoteGrpComp.encode_length]
  omega

@[simp] theorem decode_encode (message : SrqsDealResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [ResponseHeaderComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 SrqsQuoteGrpComp.encode SrqsQuoteGrpComp.decode SrqsQuoteGrpComp.decode_encode]
  simp only [Option.bind_some]
  simp only [message.srqsQuoteGrpComp.length_lt, ↓reduceDIte]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : SrqsDealResponse) : decode (encode message) = some (message, []) := by
  have trailing := decode_encode message []
  rw [List.append_nil] at trailing
  exact trailing

end SrqsDealResponse

/-- Smart Party Detail Grp Comp: 16 bytes -/
structure SmartPartyDetailGrpComp where
  partyDetailExecutingUnit : Alpha 5
  partyDetailExecutingTrader : Alpha 6
  pad5 : Alpha 5
  deriving DecidableEq, Repr

namespace SmartPartyDetailGrpComp

def encode (message : SmartPartyDetailGrpComp) : List UInt8 :=
  Alpha.encode message.partyDetailExecutingUnit
    ++ Alpha.encode message.partyDetailExecutingTrader
    ++ Alpha.encode message.pad5

def decode (bytes : List UInt8) : Option (SmartPartyDetailGrpComp × List UInt8) := do
  let (partyDetailExecutingUnit, bytes) ← Alpha.decode 5 bytes
  let (partyDetailExecutingTrader, bytes) ← Alpha.decode 6 bytes
  let (pad5, bytes) ← Alpha.decode 5 bytes
  pure ({ partyDetailExecutingUnit, partyDetailExecutingTrader, pad5 }, bytes)

@[simp] theorem encode_length (message : SmartPartyDetailGrpComp) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : SmartPartyDetailGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SmartPartyDetailGrpComp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end SmartPartyDetailGrpComp

/-- Srqs Inquire Smart Respondent Response -/
structure SrqsInquireSmartRespondentResponse where
  pad2 : Alpha 2
  responseHeaderComp : ResponseHeaderComp
  marketSegmentId : BitVec 32
  pad2v2 : Alpha 2
  smartPartyDetailGrpComp : Bounded 2 SmartPartyDetailGrpComp
  deriving DecidableEq, Repr

namespace SrqsInquireSmartRespondentResponse

def encode (message : SrqsInquireSmartRespondentResponse) : List UInt8 :=
  Alpha.encode message.pad2
    ++ ResponseHeaderComp.encode message.responseHeaderComp
    ++ encodeUIntLE 4 message.marketSegmentId
    ++ encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.smartPartyDetailGrpComp.val.length)
    ++ Alpha.encode message.pad2v2
    ++ encodeMany SmartPartyDetailGrpComp.encode message.smartPartyDetailGrpComp.val

def decode (bytes : List UInt8) : Option (SrqsInquireSmartRespondentResponse × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (responseHeaderComp, bytes) ← ResponseHeaderComp.decode bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (noPartyDetails, bytes) ← decodeUIntLE 2 bytes
  let (pad2v2, bytes) ← Alpha.decode 2 bytes
  let (smartPartyDetailGrpComp_, bytes) ← decodeMany SmartPartyDetailGrpComp.decode noPartyDetails.toNat bytes
  if fits_smartPartyDetailGrpComp : smartPartyDetailGrpComp_.length < 256 ^ 2 then
    pure ({ pad2, responseHeaderComp, marketSegmentId, pad2v2, smartPartyDetailGrpComp := ⟨smartPartyDetailGrpComp_, fits_smartPartyDetailGrpComp⟩ }, bytes)
  else none

theorem encode_length_pos (message : SrqsInquireSmartRespondentResponse) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SrqsInquireSmartRespondentResponse) : (encode message).length ≤ 1048594 := by
  have bound_smartPartyDetailGrpComp := message.smartPartyDetailGrpComp.length_lt
  unfold encode
  simp only [List.length_append, Alpha.encode_length, ResponseHeaderComp.encode_length, encodeUIntLE_length, encodeMany_length_const SmartPartyDetailGrpComp.encode 16 SmartPartyDetailGrpComp.encode_length]
  omega

@[simp] theorem decode_encode (message : SrqsInquireSmartRespondentResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [ResponseHeaderComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 2 SmartPartyDetailGrpComp.encode SmartPartyDetailGrpComp.decode SmartPartyDetailGrpComp.decode_encode]
  simp only [Option.bind_some]
  simp only [message.smartPartyDetailGrpComp.length_lt, ↓reduceDIte]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : SrqsInquireSmartRespondentResponse) : decode (encode message) = some (message, []) := by
  have trailing := decode_encode message []
  rw [List.append_nil] at trailing
  exact trailing

end SrqsInquireSmartRespondentResponse

/-- Srqs Negotiation Notification: 586 bytes -/
structure SrqsNegotiationNotification where
  pad2 : Alpha 2
  rbcHeaderComp : RbcHeaderComp
  transactTime : BitVec 64
  quoteRefPrice : BitVec 64
  underlyingDeltaPercentage : BitVec 64
  bidPx : BitVec 64
  offerPx : BitVec 64
  lastPx : BitVec 64
  leavesQty : BitVec 64
  lastQty : BitVec 64
  effectiveTime : BitVec 64
  lastUpdateTime : BitVec 64
  tradeToQuoteRatio : BitVec 64
  negotiationId : BitVec 32
  numberOfRespondents : BitVec 32
  tradeToQuoteRatioPosition : BitVec 16
  quoteType : BitVec 8
  quoteSubType : BitVec 8
  quoteInstruction : BitVec 8
  side : BitVec 8
  tradeAggregationTransType : BitVec 8
  quoteCondition : QuoteCondition
  partyExecutingFirm : Alpha 5
  partyExecutingTrader : Alpha 6
  partyEnteringTrader : Alpha 6
  targetPartyExecutingFirm : Alpha 5
  targetPartyExecutingTrader : Alpha 6
  firmNegotiationId : Alpha 20
  freeText5 : Alpha 132
  partyOrderOriginationTrader : Alpha 132
  chargeId : Alpha 132
  pad4 : Alpha 4
  deriving DecidableEq, Repr

namespace SrqsNegotiationNotification

def encode (message : SrqsNegotiationNotification) : List UInt8 :=
  Alpha.encode message.pad2
    ++ RbcHeaderComp.encode message.rbcHeaderComp
    ++ encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 8 message.quoteRefPrice
    ++ encodeUIntLE 8 message.underlyingDeltaPercentage
    ++ encodeUIntLE 8 message.bidPx
    ++ encodeUIntLE 8 message.offerPx
    ++ encodeUIntLE 8 message.lastPx
    ++ encodeUIntLE 8 message.leavesQty
    ++ encodeUIntLE 8 message.lastQty
    ++ encodeUIntLE 8 message.effectiveTime
    ++ encodeUIntLE 8 message.lastUpdateTime
    ++ encodeUIntLE 8 message.tradeToQuoteRatio
    ++ encodeUIntLE 4 message.negotiationId
    ++ encodeUIntLE 4 message.numberOfRespondents
    ++ encodeUIntLE 2 message.tradeToQuoteRatioPosition
    ++ encodeUInt 1 message.quoteType
    ++ encodeUInt 1 message.quoteSubType
    ++ encodeUInt 1 message.quoteInstruction
    ++ encodeUInt 1 message.side
    ++ encodeUInt 1 message.tradeAggregationTransType
    ++ QuoteCondition.encode message.quoteCondition
    ++ Alpha.encode message.partyExecutingFirm
    ++ Alpha.encode message.partyExecutingTrader
    ++ Alpha.encode message.partyEnteringTrader
    ++ Alpha.encode message.targetPartyExecutingFirm
    ++ Alpha.encode message.targetPartyExecutingTrader
    ++ Alpha.encode message.firmNegotiationId
    ++ Alpha.encode message.freeText5
    ++ Alpha.encode message.partyOrderOriginationTrader
    ++ Alpha.encode message.chargeId
    ++ Alpha.encode message.pad4

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (SrqsNegotiationNotification × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderComp, bytes) ← RbcHeaderComp.decode bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (quoteRefPrice, bytes) ← decodeUIntLE 8 bytes
  let (underlyingDeltaPercentage, bytes) ← decodeUIntLE 8 bytes
  let (bidPx, bytes) ← decodeUIntLE 8 bytes
  let (offerPx, bytes) ← decodeUIntLE 8 bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  let (leavesQty, bytes) ← decodeUIntLE 8 bytes
  let (lastQty, bytes) ← decodeUIntLE 8 bytes
  let (effectiveTime, bytes) ← decodeUIntLE 8 bytes
  let (lastUpdateTime, bytes) ← decodeUIntLE 8 bytes
  let (tradeToQuoteRatio, bytes) ← decodeUIntLE 8 bytes
  let (negotiationId, bytes) ← decodeUIntLE 4 bytes
  let (numberOfRespondents, bytes) ← decodeUIntLE 4 bytes
  let (tradeToQuoteRatioPosition, bytes) ← decodeUIntLE 2 bytes
  let (quoteType, bytes) ← decodeUInt 1 bytes
  let (quoteSubType, bytes) ← decodeUInt 1 bytes
  let (quoteInstruction, bytes) ← decodeUInt 1 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (tradeAggregationTransType, bytes) ← decodeUInt 1 bytes
  let (quoteCondition, bytes) ← QuoteCondition.decode bytes
  let (partyExecutingFirm, bytes) ← Alpha.decode 5 bytes
  let (partyExecutingTrader, bytes) ← Alpha.decode 6 bytes
  let (partyEnteringTrader, bytes) ← Alpha.decode 6 bytes
  let (targetPartyExecutingFirm, bytes) ← Alpha.decode 5 bytes
  let (targetPartyExecutingTrader, bytes) ← Alpha.decode 6 bytes
  let (firmNegotiationId, bytes) ← Alpha.decode 20 bytes
  let (freeText5, bytes) ← Alpha.decode 132 bytes
  let (partyOrderOriginationTrader, bytes) ← Alpha.decode 132 bytes
  let (chargeId, bytes) ← Alpha.decode 132 bytes
  let (pad4, bytes) ← Alpha.decode 4 bytes
  pure ({ pad2, rbcHeaderComp, transactTime, quoteRefPrice, underlyingDeltaPercentage, bidPx, offerPx, lastPx, leavesQty, lastQty, effectiveTime, lastUpdateTime, tradeToQuoteRatio, negotiationId, numberOfRespondents, tradeToQuoteRatioPosition, quoteType, quoteSubType, quoteInstruction, side, tradeAggregationTransType, quoteCondition, partyExecutingFirm, partyExecutingTrader, partyEnteringTrader, targetPartyExecutingFirm, targetPartyExecutingTrader, firmNegotiationId, freeText5, partyOrderOriginationTrader, chargeId, pad4 }, bytes)

@[simp] theorem encode_length (message : SrqsNegotiationNotification) : (encode message).length = 586 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RbcHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length, QuoteCondition.encode_length]

theorem encode_length_pos (message : SrqsNegotiationNotification) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SrqsNegotiationNotification) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [RbcHeaderComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [QuoteCondition.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : SrqsNegotiationNotification) : decode (encode message) = some (message, []) := by
  have trailing := decode_encode message []
  rw [List.append_nil] at trailing
  exact trailing

end SrqsNegotiationNotification

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
    ++ encodeUInt 1 message.sideDisclosureInstruction
    ++ encodeUInt 1 message.priceDisclosureInstruction
    ++ encodeUInt 1 message.leavesQtyDisclosureInstruction
    ++ encodeUInt 1 message.lastPxDisclosureInstruction
    ++ encodeUInt 1 message.lastQtyDisclosureInstruction
    ++ encodeUInt 1 message.freeText5DisclosureInstruction
    ++ encodeUInt 1 message.partyOrderOriginationDisclosureInstruction
    ++ encodeUInt 1 message.quoteInstruction
    ++ encodeUInt 1 message.chargeIdDisclosureInstruction
    ++ Alpha.encode message.targetPartyExecutingFirm
    ++ Alpha.encode message.targetPartyExecutingTrader
    ++ encodeUInt 1 message.partyDetailStatus
    ++ encodeUInt 1 message.partyDetailStatusInformation
    ++ Alpha.encode message.pad6

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
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end TargetPartiesComp

/-- Srqs Negotiation Requester Notification -/
structure SrqsNegotiationRequesterNotification where
  pad2 : Alpha 2
  rbcHeaderComp : RbcHeaderComp
  transactTime : BitVec 64
  trdRegTsExecutionTime : BitVec 64
  quoteRefPrice : BitVec 64
  underlyingDeltaPercentage : BitVec 64
  bidPx : BitVec 64
  offerPx : BitVec 64
  orderQty : BitVec 64
  lastPx : BitVec 64
  leavesQty : BitVec 64
  lastQty : BitVec 64
  effectiveTime : BitVec 64
  lastUpdateTime : BitVec 64
  tradeToRequestRatio : BitVec 64
  negotiationId : BitVec 32
  numberOfRespondents : BitVec 32
  quoteType : BitVec 8
  quoteSubType : BitVec 8
  respondentType : BitVec 8
  numberOfRespDisclosureInstruction : BitVec 8
  side : BitVec 8
  showLastDealOnClosure : BitVec 8
  tradeAggregationTransType : BitVec 8
  quoteCondition : QuoteCondition
  partyExecutingFirm : Alpha 5
  partyExecutingTrader : Alpha 6
  partyEnteringTrader : Alpha 6
  firmNegotiationId : Alpha 20
  freeText5 : Alpha 132
  partyOrderOriginationTrader : Alpha 132
  chargeId : Alpha 132
  pad6 : Alpha 6
  targetPartiesComp : Bounded 1 TargetPartiesComp
  deriving DecidableEq, Repr

namespace SrqsNegotiationRequesterNotification

def encode (message : SrqsNegotiationRequesterNotification) : List UInt8 :=
  Alpha.encode message.pad2
    ++ RbcHeaderComp.encode message.rbcHeaderComp
    ++ encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 8 message.trdRegTsExecutionTime
    ++ encodeUIntLE 8 message.quoteRefPrice
    ++ encodeUIntLE 8 message.underlyingDeltaPercentage
    ++ encodeUIntLE 8 message.bidPx
    ++ encodeUIntLE 8 message.offerPx
    ++ encodeUIntLE 8 message.orderQty
    ++ encodeUIntLE 8 message.lastPx
    ++ encodeUIntLE 8 message.leavesQty
    ++ encodeUIntLE 8 message.lastQty
    ++ encodeUIntLE 8 message.effectiveTime
    ++ encodeUIntLE 8 message.lastUpdateTime
    ++ encodeUIntLE 8 message.tradeToRequestRatio
    ++ encodeUIntLE 4 message.negotiationId
    ++ encodeUIntLE 4 message.numberOfRespondents
    ++ encodeUInt 1 message.quoteType
    ++ encodeUInt 1 message.quoteSubType
    ++ encodeUInt 1 message.respondentType
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.targetPartiesComp.val.length)
    ++ encodeUInt 1 message.numberOfRespDisclosureInstruction
    ++ encodeUInt 1 message.side
    ++ encodeUInt 1 message.showLastDealOnClosure
    ++ encodeUInt 1 message.tradeAggregationTransType
    ++ QuoteCondition.encode message.quoteCondition
    ++ Alpha.encode message.partyExecutingFirm
    ++ Alpha.encode message.partyExecutingTrader
    ++ Alpha.encode message.partyEnteringTrader
    ++ Alpha.encode message.firmNegotiationId
    ++ Alpha.encode message.freeText5
    ++ Alpha.encode message.partyOrderOriginationTrader
    ++ Alpha.encode message.chargeId
    ++ Alpha.encode message.pad6
    ++ encodeMany TargetPartiesComp.encode message.targetPartiesComp.val

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (SrqsNegotiationRequesterNotification × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderComp, bytes) ← RbcHeaderComp.decode bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (trdRegTsExecutionTime, bytes) ← decodeUIntLE 8 bytes
  let (quoteRefPrice, bytes) ← decodeUIntLE 8 bytes
  let (underlyingDeltaPercentage, bytes) ← decodeUIntLE 8 bytes
  let (bidPx, bytes) ← decodeUIntLE 8 bytes
  let (offerPx, bytes) ← decodeUIntLE 8 bytes
  let (orderQty, bytes) ← decodeUIntLE 8 bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  let (leavesQty, bytes) ← decodeUIntLE 8 bytes
  let (lastQty, bytes) ← decodeUIntLE 8 bytes
  let (effectiveTime, bytes) ← decodeUIntLE 8 bytes
  let (lastUpdateTime, bytes) ← decodeUIntLE 8 bytes
  let (tradeToRequestRatio, bytes) ← decodeUIntLE 8 bytes
  let (negotiationId, bytes) ← decodeUIntLE 4 bytes
  let (numberOfRespondents, bytes) ← decodeUIntLE 4 bytes
  let (quoteType, bytes) ← decodeUInt 1 bytes
  let (quoteSubType, bytes) ← decodeUInt 1 bytes
  let (respondentType, bytes) ← decodeUInt 1 bytes
  let (noTargetPartyIDs, bytes) ← decodeUInt 1 bytes
  let (numberOfRespDisclosureInstruction, bytes) ← decodeUInt 1 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (showLastDealOnClosure, bytes) ← decodeUInt 1 bytes
  let (tradeAggregationTransType, bytes) ← decodeUInt 1 bytes
  let (quoteCondition, bytes) ← QuoteCondition.decode bytes
  let (partyExecutingFirm, bytes) ← Alpha.decode 5 bytes
  let (partyExecutingTrader, bytes) ← Alpha.decode 6 bytes
  let (partyEnteringTrader, bytes) ← Alpha.decode 6 bytes
  let (firmNegotiationId, bytes) ← Alpha.decode 20 bytes
  let (freeText5, bytes) ← Alpha.decode 132 bytes
  let (partyOrderOriginationTrader, bytes) ← Alpha.decode 132 bytes
  let (chargeId, bytes) ← Alpha.decode 132 bytes
  let (pad6, bytes) ← Alpha.decode 6 bytes
  let (targetPartiesComp_, bytes) ← decodeMany TargetPartiesComp.decode noTargetPartyIDs.toNat bytes
  if fits_targetPartiesComp : targetPartiesComp_.length < 256 ^ 1 then
    pure ({ pad2, rbcHeaderComp, transactTime, trdRegTsExecutionTime, quoteRefPrice, underlyingDeltaPercentage, bidPx, offerPx, orderQty, lastPx, leavesQty, lastQty, effectiveTime, lastUpdateTime, tradeToRequestRatio, negotiationId, numberOfRespondents, quoteType, quoteSubType, respondentType, numberOfRespDisclosureInstruction, side, showLastDealOnClosure, tradeAggregationTransType, quoteCondition, partyExecutingFirm, partyExecutingTrader, partyEnteringTrader, firmNegotiationId, freeText5, partyOrderOriginationTrader, chargeId, pad6, targetPartiesComp := ⟨targetPartiesComp_, fits_targetPartiesComp⟩ }, bytes)
  else none

theorem encode_length_pos (message : SrqsNegotiationRequesterNotification) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SrqsNegotiationRequesterNotification) : (encode message).length ≤ 8754 := by
  have bound_targetPartiesComp := message.targetPartiesComp.length_lt
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RbcHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length, QuoteCondition.encode_length, encodeMany_length_const TargetPartiesComp.encode 32 TargetPartiesComp.encode_length]
  omega

@[simp] theorem decode_encode (message : SrqsNegotiationRequesterNotification) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [RbcHeaderComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [QuoteCondition.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 TargetPartiesComp.encode TargetPartiesComp.decode TargetPartiesComp.decode_encode]
  simp only [Option.bind_some]
  simp only [message.targetPartiesComp.length_lt, ↓reduceDIte]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : SrqsNegotiationRequesterNotification) : decode (encode message) = some (message, []) := by
  have trailing := decode_encode message []
  rw [List.append_nil] at trailing
  exact trailing

end SrqsNegotiationRequesterNotification

/-- Srqs Negotiation Status Notification: 82 bytes -/
structure SrqsNegotiationStatusNotification where
  pad2 : Alpha 2
  rbcHeaderComp : RbcHeaderComp
  transactTime : BitVec 64
  effectiveTime : BitVec 64
  negotiationId : BitVec 32
  quoteCondition : QuoteCondition
  firmNegotiationId : Alpha 20
  pad7 : Alpha 7
  deriving DecidableEq, Repr

namespace SrqsNegotiationStatusNotification

def encode (message : SrqsNegotiationStatusNotification) : List UInt8 :=
  Alpha.encode message.pad2
    ++ RbcHeaderComp.encode message.rbcHeaderComp
    ++ encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 8 message.effectiveTime
    ++ encodeUIntLE 4 message.negotiationId
    ++ QuoteCondition.encode message.quoteCondition
    ++ Alpha.encode message.firmNegotiationId
    ++ Alpha.encode message.pad7

def decode (bytes : List UInt8) : Option (SrqsNegotiationStatusNotification × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderComp, bytes) ← RbcHeaderComp.decode bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (effectiveTime, bytes) ← decodeUIntLE 8 bytes
  let (negotiationId, bytes) ← decodeUIntLE 4 bytes
  let (quoteCondition, bytes) ← QuoteCondition.decode bytes
  let (firmNegotiationId, bytes) ← Alpha.decode 20 bytes
  let (pad7, bytes) ← Alpha.decode 7 bytes
  pure ({ pad2, rbcHeaderComp, transactTime, effectiveTime, negotiationId, quoteCondition, firmNegotiationId, pad7 }, bytes)

@[simp] theorem encode_length (message : SrqsNegotiationStatusNotification) : (encode message).length = 82 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RbcHeaderComp.encode_length, encodeUIntLE_length, QuoteCondition.encode_length]

theorem encode_length_pos (message : SrqsNegotiationStatusNotification) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SrqsNegotiationStatusNotification) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [RbcHeaderComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [QuoteCondition.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : SrqsNegotiationStatusNotification) : decode (encode message) = some (message, []) := by
  have trailing := decode_encode message []
  rw [List.append_nil] at trailing
  exact trailing

end SrqsNegotiationStatusNotification

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
    ++ encodeUIntLE 4 message.legRatioQty
    ++ encodeUIntLE 4 message.legSymbol
    ++ encodeUInt 1 message.legSecurityType
    ++ encodeUInt 1 message.legSide
    ++ Alpha.encode message.pad6

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
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end QuotReqLegsGrpComp

/-- Srqs Open Negotiation Notification -/
structure SrqsOpenNegotiationNotification where
  pad2 : Alpha 2
  rbcHeaderComp : RbcHeaderComp
  transactTime : BitVec 64
  negotiationStartTime : BitVec 64
  securityId : BitVec 64
  bidPx : BitVec 64
  offerPx : BitVec 64
  leavesQty : BitVec 64
  lastQty : BitVec 64
  lastPx : BitVec 64
  quoteRefPrice : BitVec 64
  underlyingDeltaPercentage : BitVec 64
  expireTime : BitVec 64
  tradeToRequestRatio : BitVec 64
  tradeToQuoteRatio : BitVec 64
  negotiationId : BitVec 32
  marketSegmentId : BitVec 32
  securitySubType : BitVec 32
  numberOfRespondents : BitVec 32
  tradeToQuoteRatioPosition : BitVec 16
  quoteType : BitVec 8
  quoteSubType : BitVec 8
  side : BitVec 8
  productComplex : BitVec 8
  respondentType : BitVec 8
  tradeAggregationTransType : BitVec 8
  quoteCondition : QuoteCondition
  partyExecutingFirm : Alpha 5
  partyExecutingTrader : Alpha 6
  partyEnteringTrader : Alpha 6
  targetPartyExecutingFirm : Alpha 5
  targetPartyExecutingTrader : Alpha 6
  firmNegotiationId : Alpha 20
  freeText5 : Alpha 132
  partyOrderOriginationTrader : Alpha 132
  chargeId : Alpha 132
  pad2v2 : Alpha 2
  quotReqLegsGrpComp : Bounded 1 QuotReqLegsGrpComp
  deriving DecidableEq, Repr

namespace SrqsOpenNegotiationNotification

def encode (message : SrqsOpenNegotiationNotification) : List UInt8 :=
  Alpha.encode message.pad2
    ++ RbcHeaderComp.encode message.rbcHeaderComp
    ++ encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 8 message.negotiationStartTime
    ++ encodeUIntLE 8 message.securityId
    ++ encodeUIntLE 8 message.bidPx
    ++ encodeUIntLE 8 message.offerPx
    ++ encodeUIntLE 8 message.leavesQty
    ++ encodeUIntLE 8 message.lastQty
    ++ encodeUIntLE 8 message.lastPx
    ++ encodeUIntLE 8 message.quoteRefPrice
    ++ encodeUIntLE 8 message.underlyingDeltaPercentage
    ++ encodeUIntLE 8 message.expireTime
    ++ encodeUIntLE 8 message.tradeToRequestRatio
    ++ encodeUIntLE 8 message.tradeToQuoteRatio
    ++ encodeUIntLE 4 message.negotiationId
    ++ encodeUIntLE 4 message.marketSegmentId
    ++ encodeUIntLE 4 message.securitySubType
    ++ encodeUIntLE 4 message.numberOfRespondents
    ++ encodeUIntLE 2 message.tradeToQuoteRatioPosition
    ++ encodeUInt 1 message.quoteType
    ++ encodeUInt 1 message.quoteSubType
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.quotReqLegsGrpComp.val.length)
    ++ encodeUInt 1 message.side
    ++ encodeUInt 1 message.productComplex
    ++ encodeUInt 1 message.respondentType
    ++ encodeUInt 1 message.tradeAggregationTransType
    ++ QuoteCondition.encode message.quoteCondition
    ++ Alpha.encode message.partyExecutingFirm
    ++ Alpha.encode message.partyExecutingTrader
    ++ Alpha.encode message.partyEnteringTrader
    ++ Alpha.encode message.targetPartyExecutingFirm
    ++ Alpha.encode message.targetPartyExecutingTrader
    ++ Alpha.encode message.firmNegotiationId
    ++ Alpha.encode message.freeText5
    ++ Alpha.encode message.partyOrderOriginationTrader
    ++ Alpha.encode message.chargeId
    ++ Alpha.encode message.pad2v2
    ++ encodeMany QuotReqLegsGrpComp.encode message.quotReqLegsGrpComp.val

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (SrqsOpenNegotiationNotification × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderComp, bytes) ← RbcHeaderComp.decode bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (negotiationStartTime, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (bidPx, bytes) ← decodeUIntLE 8 bytes
  let (offerPx, bytes) ← decodeUIntLE 8 bytes
  let (leavesQty, bytes) ← decodeUIntLE 8 bytes
  let (lastQty, bytes) ← decodeUIntLE 8 bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  let (quoteRefPrice, bytes) ← decodeUIntLE 8 bytes
  let (underlyingDeltaPercentage, bytes) ← decodeUIntLE 8 bytes
  let (expireTime, bytes) ← decodeUIntLE 8 bytes
  let (tradeToRequestRatio, bytes) ← decodeUIntLE 8 bytes
  let (tradeToQuoteRatio, bytes) ← decodeUIntLE 8 bytes
  let (negotiationId, bytes) ← decodeUIntLE 4 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (securitySubType, bytes) ← decodeUIntLE 4 bytes
  let (numberOfRespondents, bytes) ← decodeUIntLE 4 bytes
  let (tradeToQuoteRatioPosition, bytes) ← decodeUIntLE 2 bytes
  let (quoteType, bytes) ← decodeUInt 1 bytes
  let (quoteSubType, bytes) ← decodeUInt 1 bytes
  let (noLegs, bytes) ← decodeUInt 1 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (productComplex, bytes) ← decodeUInt 1 bytes
  let (respondentType, bytes) ← decodeUInt 1 bytes
  let (tradeAggregationTransType, bytes) ← decodeUInt 1 bytes
  let (quoteCondition, bytes) ← QuoteCondition.decode bytes
  let (partyExecutingFirm, bytes) ← Alpha.decode 5 bytes
  let (partyExecutingTrader, bytes) ← Alpha.decode 6 bytes
  let (partyEnteringTrader, bytes) ← Alpha.decode 6 bytes
  let (targetPartyExecutingFirm, bytes) ← Alpha.decode 5 bytes
  let (targetPartyExecutingTrader, bytes) ← Alpha.decode 6 bytes
  let (firmNegotiationId, bytes) ← Alpha.decode 20 bytes
  let (freeText5, bytes) ← Alpha.decode 132 bytes
  let (partyOrderOriginationTrader, bytes) ← Alpha.decode 132 bytes
  let (chargeId, bytes) ← Alpha.decode 132 bytes
  let (pad2v2, bytes) ← Alpha.decode 2 bytes
  let (quotReqLegsGrpComp_, bytes) ← decodeMany QuotReqLegsGrpComp.decode noLegs.toNat bytes
  if fits_quotReqLegsGrpComp : quotReqLegsGrpComp_.length < 256 ^ 1 then
    pure ({ pad2, rbcHeaderComp, transactTime, negotiationStartTime, securityId, bidPx, offerPx, leavesQty, lastQty, lastPx, quoteRefPrice, underlyingDeltaPercentage, expireTime, tradeToRequestRatio, tradeToQuoteRatio, negotiationId, marketSegmentId, securitySubType, numberOfRespondents, tradeToQuoteRatioPosition, quoteType, quoteSubType, side, productComplex, respondentType, tradeAggregationTransType, quoteCondition, partyExecutingFirm, partyExecutingTrader, partyEnteringTrader, targetPartyExecutingFirm, targetPartyExecutingTrader, firmNegotiationId, freeText5, partyOrderOriginationTrader, chargeId, pad2v2, quotReqLegsGrpComp := ⟨quotReqLegsGrpComp_, fits_quotReqLegsGrpComp⟩ }, bytes)
  else none

theorem encode_length_pos (message : SrqsOpenNegotiationNotification) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SrqsOpenNegotiationNotification) : (encode message).length ≤ 6730 := by
  have bound_quotReqLegsGrpComp := message.quotReqLegsGrpComp.length_lt
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RbcHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length, QuoteCondition.encode_length, encodeMany_length_const QuotReqLegsGrpComp.encode 24 QuotReqLegsGrpComp.encode_length]
  omega

@[simp] theorem decode_encode (message : SrqsOpenNegotiationNotification) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [RbcHeaderComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [QuoteCondition.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 QuotReqLegsGrpComp.encode QuotReqLegsGrpComp.decode QuotReqLegsGrpComp.decode_encode]
  simp only [Option.bind_some]
  simp only [message.quotReqLegsGrpComp.length_lt, ↓reduceDIte]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : SrqsOpenNegotiationNotification) : decode (encode message) = some (message, []) := by
  have trailing := decode_encode message []
  rw [List.append_nil] at trailing
  exact trailing

end SrqsOpenNegotiationNotification

/-- Srqs Open Negotiation Requester Notification -/
structure SrqsOpenNegotiationRequesterNotification where
  pad2 : Alpha 2
  rbcHeaderComp : RbcHeaderComp
  transactTime : BitVec 64
  securityId : BitVec 64
  bidPx : BitVec 64
  offerPx : BitVec 64
  orderQty : BitVec 64
  lastPx : BitVec 64
  lastQty : BitVec 64
  quoteRefPrice : BitVec 64
  underlyingDeltaPercentage : BitVec 64
  expireTime : BitVec 64
  tradeToRequestRatio : BitVec 64
  negotiationId : BitVec 32
  marketSegmentId : BitVec 32
  securitySubType : BitVec 32
  numberOfRespondents : BitVec 32
  quoteType : BitVec 8
  quoteSubType : BitVec 8
  side : BitVec 8
  productComplex : BitVec 8
  numberOfRespDisclosureInstruction : BitVec 8
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
  partyEnteringTrader : Alpha 6
  firmNegotiationId : Alpha 20
  freeText5 : Alpha 132
  partyOrderOriginationTrader : Alpha 132
  chargeId : Alpha 132
  quotReqLegsGrpComp : Bounded 1 QuotReqLegsGrpComp
  targetPartiesComp : Bounded 1 TargetPartiesComp
  deriving DecidableEq, Repr

namespace SrqsOpenNegotiationRequesterNotification

def encode (message : SrqsOpenNegotiationRequesterNotification) : List UInt8 :=
  Alpha.encode message.pad2
    ++ RbcHeaderComp.encode message.rbcHeaderComp
    ++ encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 8 message.securityId
    ++ encodeUIntLE 8 message.bidPx
    ++ encodeUIntLE 8 message.offerPx
    ++ encodeUIntLE 8 message.orderQty
    ++ encodeUIntLE 8 message.lastPx
    ++ encodeUIntLE 8 message.lastQty
    ++ encodeUIntLE 8 message.quoteRefPrice
    ++ encodeUIntLE 8 message.underlyingDeltaPercentage
    ++ encodeUIntLE 8 message.expireTime
    ++ encodeUIntLE 8 message.tradeToRequestRatio
    ++ encodeUIntLE 4 message.negotiationId
    ++ encodeUIntLE 4 message.marketSegmentId
    ++ encodeUIntLE 4 message.securitySubType
    ++ encodeUIntLE 4 message.numberOfRespondents
    ++ encodeUInt 1 message.quoteType
    ++ encodeUInt 1 message.quoteSubType
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.quotReqLegsGrpComp.val.length)
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.targetPartiesComp.val.length)
    ++ encodeUInt 1 message.side
    ++ encodeUInt 1 message.productComplex
    ++ encodeUInt 1 message.numberOfRespDisclosureInstruction
    ++ encodeUInt 1 message.respondentType
    ++ encodeUInt 1 message.showLastDealOnClosure
    ++ encodeUInt 1 message.bidPxIsLocked
    ++ encodeUInt 1 message.offerPxIsLocked
    ++ encodeUInt 1 message.sideIsLocked
    ++ encodeUInt 1 message.orderQtyIsLocked
    ++ encodeUInt 1 message.tradeAggregationTransType
    ++ QuoteCondition.encode message.quoteCondition
    ++ Alpha.encode message.partyExecutingFirm
    ++ Alpha.encode message.partyExecutingTrader
    ++ Alpha.encode message.partyEnteringTrader
    ++ Alpha.encode message.firmNegotiationId
    ++ Alpha.encode message.freeText5
    ++ Alpha.encode message.partyOrderOriginationTrader
    ++ Alpha.encode message.chargeId
    ++ encodeMany QuotReqLegsGrpComp.encode message.quotReqLegsGrpComp.val
    ++ encodeMany TargetPartiesComp.encode message.targetPartiesComp.val

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (SrqsOpenNegotiationRequesterNotification × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderComp, bytes) ← RbcHeaderComp.decode bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (bidPx, bytes) ← decodeUIntLE 8 bytes
  let (offerPx, bytes) ← decodeUIntLE 8 bytes
  let (orderQty, bytes) ← decodeUIntLE 8 bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  let (lastQty, bytes) ← decodeUIntLE 8 bytes
  let (quoteRefPrice, bytes) ← decodeUIntLE 8 bytes
  let (underlyingDeltaPercentage, bytes) ← decodeUIntLE 8 bytes
  let (expireTime, bytes) ← decodeUIntLE 8 bytes
  let (tradeToRequestRatio, bytes) ← decodeUIntLE 8 bytes
  let (negotiationId, bytes) ← decodeUIntLE 4 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (securitySubType, bytes) ← decodeUIntLE 4 bytes
  let (numberOfRespondents, bytes) ← decodeUIntLE 4 bytes
  let (quoteType, bytes) ← decodeUInt 1 bytes
  let (quoteSubType, bytes) ← decodeUInt 1 bytes
  let (noLegs, bytes) ← decodeUInt 1 bytes
  let (noTargetPartyIDs, bytes) ← decodeUInt 1 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (productComplex, bytes) ← decodeUInt 1 bytes
  let (numberOfRespDisclosureInstruction, bytes) ← decodeUInt 1 bytes
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
  let (partyEnteringTrader, bytes) ← Alpha.decode 6 bytes
  let (firmNegotiationId, bytes) ← Alpha.decode 20 bytes
  let (freeText5, bytes) ← Alpha.decode 132 bytes
  let (partyOrderOriginationTrader, bytes) ← Alpha.decode 132 bytes
  let (chargeId, bytes) ← Alpha.decode 132 bytes
  let (quotReqLegsGrpComp_, bytes) ← decodeMany QuotReqLegsGrpComp.decode noLegs.toNat bytes
  let (targetPartiesComp_, bytes) ← decodeMany TargetPartiesComp.decode noTargetPartyIDs.toNat bytes
  if fits_quotReqLegsGrpComp : quotReqLegsGrpComp_.length < 256 ^ 1 then
    if fits_targetPartiesComp : targetPartiesComp_.length < 256 ^ 1 then
      pure ({ pad2, rbcHeaderComp, transactTime, securityId, bidPx, offerPx, orderQty, lastPx, lastQty, quoteRefPrice, underlyingDeltaPercentage, expireTime, tradeToRequestRatio, negotiationId, marketSegmentId, securitySubType, numberOfRespondents, quoteType, quoteSubType, side, productComplex, numberOfRespDisclosureInstruction, respondentType, showLastDealOnClosure, bidPxIsLocked, offerPxIsLocked, sideIsLocked, orderQtyIsLocked, tradeAggregationTransType, quoteCondition, partyExecutingFirm, partyExecutingTrader, partyEnteringTrader, firmNegotiationId, freeText5, partyOrderOriginationTrader, chargeId, quotReqLegsGrpComp := ⟨quotReqLegsGrpComp_, fits_quotReqLegsGrpComp⟩, targetPartiesComp := ⟨targetPartiesComp_, fits_targetPartiesComp⟩ }, bytes)
    else none
  else none

theorem encode_length_pos (message : SrqsOpenNegotiationRequesterNotification) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SrqsOpenNegotiationRequesterNotification) : (encode message).length ≤ 14866 := by
  have bound_quotReqLegsGrpComp := message.quotReqLegsGrpComp.length_lt
  have bound_targetPartiesComp := message.targetPartiesComp.length_lt
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RbcHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length, QuoteCondition.encode_length, encodeMany_length_const QuotReqLegsGrpComp.encode 24 QuotReqLegsGrpComp.encode_length, encodeMany_length_const TargetPartiesComp.encode 32 TargetPartiesComp.encode_length]
  omega

@[simp] theorem decode_encode (message : SrqsOpenNegotiationRequesterNotification) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [RbcHeaderComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [QuoteCondition.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 QuotReqLegsGrpComp.encode QuotReqLegsGrpComp.decode QuotReqLegsGrpComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 TargetPartiesComp.encode TargetPartiesComp.decode TargetPartiesComp.decode_encode]
  simp only [Option.bind_some]
  simp only [message.quotReqLegsGrpComp.length_lt, message.targetPartiesComp.length_lt, ↓reduceDIte]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : SrqsOpenNegotiationRequesterNotification) : decode (encode message) = some (message, []) := by
  have trailing := decode_encode message []
  rw [List.append_nil] at trailing
  exact trailing

end SrqsOpenNegotiationRequesterNotification

/-- Srqs Quote Notification: 410 bytes -/
structure SrqsQuoteNotification where
  pad2 : Alpha 2
  rbcHeaderComp : RbcHeaderComp
  transactTime : BitVec 64
  quoteId : BitVec 64
  secondaryQuoteId : BitVec 64
  bidPx : BitVec 64
  bidSize : BitVec 64
  offerPx : BitVec 64
  offerSize : BitVec 64
  underlyingDeltaPercentage : BitVec 64
  quoteRefPrice : BitVec 64
  expireTime : BitVec 64
  negotiationId : BitVec 32
  quotingStatus : BitVec 8
  messageEventSource : MessageEventSource
  tradingCapacity : BitVec 8
  quoteCancelReason : BitVec 8
  partyIdExecutingTrader : BitVec 32
  partyExecutingFirm : Alpha 5
  partyExecutingTrader : Alpha 6
  partyEnteringTrader : Alpha 6
  quoteReqId : Alpha 20
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
  deriving DecidableEq, Repr

namespace SrqsQuoteNotification

def encode (message : SrqsQuoteNotification) : List UInt8 :=
  Alpha.encode message.pad2
    ++ RbcHeaderComp.encode message.rbcHeaderComp
    ++ encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 8 message.quoteId
    ++ encodeUIntLE 8 message.secondaryQuoteId
    ++ encodeUIntLE 8 message.bidPx
    ++ encodeUIntLE 8 message.bidSize
    ++ encodeUIntLE 8 message.offerPx
    ++ encodeUIntLE 8 message.offerSize
    ++ encodeUIntLE 8 message.underlyingDeltaPercentage
    ++ encodeUIntLE 8 message.quoteRefPrice
    ++ encodeUIntLE 8 message.expireTime
    ++ encodeUIntLE 4 message.negotiationId
    ++ encodeUInt 1 message.quotingStatus
    ++ MessageEventSource.encode message.messageEventSource
    ++ encodeUInt 1 message.tradingCapacity
    ++ encodeUInt 1 message.quoteCancelReason
    ++ encodeUIntLE 4 message.partyIdExecutingTrader
    ++ Alpha.encode message.partyExecutingFirm
    ++ Alpha.encode message.partyExecutingTrader
    ++ Alpha.encode message.partyEnteringTrader
    ++ Alpha.encode message.quoteReqId
    ++ Alpha.encode message.freeText1
    ++ Alpha.encode message.freeText2
    ++ Alpha.encode message.freeText3
    ++ Alpha.encode message.freeText5
    ++ PositionEffect.encode message.positionEffect
    ++ Alpha.encode message.account
    ++ Alpha.encode message.partyIdBeneficiary
    ++ CustOrderHandlingInst.encode message.custOrderHandlingInst
    ++ Alpha.encode message.partyIdOrderOriginationFirm
    ++ Alpha.encode message.partyIdPositionAccount
    ++ Alpha.encode message.partyIdLocationId
    ++ Alpha.encode message.complianceText
    ++ Alpha.encode message.partyIdTakeUpTradingFirm

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (SrqsQuoteNotification × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderComp, bytes) ← RbcHeaderComp.decode bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (quoteId, bytes) ← decodeUIntLE 8 bytes
  let (secondaryQuoteId, bytes) ← decodeUIntLE 8 bytes
  let (bidPx, bytes) ← decodeUIntLE 8 bytes
  let (bidSize, bytes) ← decodeUIntLE 8 bytes
  let (offerPx, bytes) ← decodeUIntLE 8 bytes
  let (offerSize, bytes) ← decodeUIntLE 8 bytes
  let (underlyingDeltaPercentage, bytes) ← decodeUIntLE 8 bytes
  let (quoteRefPrice, bytes) ← decodeUIntLE 8 bytes
  let (expireTime, bytes) ← decodeUIntLE 8 bytes
  let (negotiationId, bytes) ← decodeUIntLE 4 bytes
  let (quotingStatus, bytes) ← decodeUInt 1 bytes
  let (messageEventSource, bytes) ← MessageEventSource.decode bytes
  let (tradingCapacity, bytes) ← decodeUInt 1 bytes
  let (quoteCancelReason, bytes) ← decodeUInt 1 bytes
  let (partyIdExecutingTrader, bytes) ← decodeUIntLE 4 bytes
  let (partyExecutingFirm, bytes) ← Alpha.decode 5 bytes
  let (partyExecutingTrader, bytes) ← Alpha.decode 6 bytes
  let (partyEnteringTrader, bytes) ← Alpha.decode 6 bytes
  let (quoteReqId, bytes) ← Alpha.decode 20 bytes
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
  pure ({ pad2, rbcHeaderComp, transactTime, quoteId, secondaryQuoteId, bidPx, bidSize, offerPx, offerSize, underlyingDeltaPercentage, quoteRefPrice, expireTime, negotiationId, quotingStatus, messageEventSource, tradingCapacity, quoteCancelReason, partyIdExecutingTrader, partyExecutingFirm, partyExecutingTrader, partyEnteringTrader, quoteReqId, freeText1, freeText2, freeText3, freeText5, positionEffect, account, partyIdBeneficiary, custOrderHandlingInst, partyIdOrderOriginationFirm, partyIdPositionAccount, partyIdLocationId, complianceText, partyIdTakeUpTradingFirm }, bytes)

@[simp] theorem encode_length (message : SrqsQuoteNotification) : (encode message).length = 410 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RbcHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length, MessageEventSource.encode_length, PositionEffect.encode_length, CustOrderHandlingInst.encode_length]

theorem encode_length_pos (message : SrqsQuoteNotification) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SrqsQuoteNotification) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [RbcHeaderComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [MessageEventSource.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [PositionEffect.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [CustOrderHandlingInst.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : SrqsQuoteNotification) : decode (encode message) = some (message, []) := by
  have trailing := decode_encode message []
  rw [List.append_nil] at trailing
  exact trailing

end SrqsQuoteNotification

/-- Srqs Quote Response: 58 bytes -/
structure SrqsQuoteResponse where
  pad2 : Alpha 2
  responseHeaderComp : ResponseHeaderComp
  quoteId : BitVec 64
  negotiationId : BitVec 32
  quoteReqId : Alpha 20
  deriving DecidableEq, Repr

namespace SrqsQuoteResponse

def encode (message : SrqsQuoteResponse) : List UInt8 :=
  Alpha.encode message.pad2
    ++ ResponseHeaderComp.encode message.responseHeaderComp
    ++ encodeUIntLE 8 message.quoteId
    ++ encodeUIntLE 4 message.negotiationId
    ++ Alpha.encode message.quoteReqId

def decode (bytes : List UInt8) : Option (SrqsQuoteResponse × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (responseHeaderComp, bytes) ← ResponseHeaderComp.decode bytes
  let (quoteId, bytes) ← decodeUIntLE 8 bytes
  let (negotiationId, bytes) ← decodeUIntLE 4 bytes
  let (quoteReqId, bytes) ← Alpha.decode 20 bytes
  pure ({ pad2, responseHeaderComp, quoteId, negotiationId, quoteReqId }, bytes)

@[simp] theorem encode_length (message : SrqsQuoteResponse) : (encode message).length = 58 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, ResponseHeaderComp.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : SrqsQuoteResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SrqsQuoteResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [ResponseHeaderComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : SrqsQuoteResponse) : decode (encode message) = some (message, []) := by
  have trailing := decode_encode message []
  rw [List.append_nil] at trailing
  exact trailing

end SrqsQuoteResponse

/-- Srqs Quote Entry Grp Comp: 136 bytes -/
structure SrqsQuoteEntryGrpComp where
  transactTime : BitVec 64
  expireTime : BitVec 64
  quoteId : BitVec 64
  secondaryQuoteId : BitVec 64
  bidPx : BitVec 64
  bidSize : BitVec 64
  offerPx : BitVec 64
  offerSize : BitVec 64
  underlyingPx : BitVec 64
  underlyingDeltaPercentage : BitVec 64
  quoteRefPrice : BitVec 64
  partyIdExecutingTrader : BitVec 32
  negotiationId : BitVec 32
  quotingStatus : BitVec 8
  firmNegotiationId : Alpha 20
  partyExecutingFirm : Alpha 5
  partyExecutingTrader : Alpha 6
  partyEnteringTrader : Alpha 6
  pad2 : Alpha 2
  deriving DecidableEq, Repr

namespace SrqsQuoteEntryGrpComp

def encode (message : SrqsQuoteEntryGrpComp) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 8 message.expireTime
    ++ encodeUIntLE 8 message.quoteId
    ++ encodeUIntLE 8 message.secondaryQuoteId
    ++ encodeUIntLE 8 message.bidPx
    ++ encodeUIntLE 8 message.bidSize
    ++ encodeUIntLE 8 message.offerPx
    ++ encodeUIntLE 8 message.offerSize
    ++ encodeUIntLE 8 message.underlyingPx
    ++ encodeUIntLE 8 message.underlyingDeltaPercentage
    ++ encodeUIntLE 8 message.quoteRefPrice
    ++ encodeUIntLE 4 message.partyIdExecutingTrader
    ++ encodeUIntLE 4 message.negotiationId
    ++ encodeUInt 1 message.quotingStatus
    ++ Alpha.encode message.firmNegotiationId
    ++ Alpha.encode message.partyExecutingFirm
    ++ Alpha.encode message.partyExecutingTrader
    ++ Alpha.encode message.partyEnteringTrader
    ++ Alpha.encode message.pad2

def decode (bytes : List UInt8) : Option (SrqsQuoteEntryGrpComp × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (expireTime, bytes) ← decodeUIntLE 8 bytes
  let (quoteId, bytes) ← decodeUIntLE 8 bytes
  let (secondaryQuoteId, bytes) ← decodeUIntLE 8 bytes
  let (bidPx, bytes) ← decodeUIntLE 8 bytes
  let (bidSize, bytes) ← decodeUIntLE 8 bytes
  let (offerPx, bytes) ← decodeUIntLE 8 bytes
  let (offerSize, bytes) ← decodeUIntLE 8 bytes
  let (underlyingPx, bytes) ← decodeUIntLE 8 bytes
  let (underlyingDeltaPercentage, bytes) ← decodeUIntLE 8 bytes
  let (quoteRefPrice, bytes) ← decodeUIntLE 8 bytes
  let (partyIdExecutingTrader, bytes) ← decodeUIntLE 4 bytes
  let (negotiationId, bytes) ← decodeUIntLE 4 bytes
  let (quotingStatus, bytes) ← decodeUInt 1 bytes
  let (firmNegotiationId, bytes) ← Alpha.decode 20 bytes
  let (partyExecutingFirm, bytes) ← Alpha.decode 5 bytes
  let (partyExecutingTrader, bytes) ← Alpha.decode 6 bytes
  let (partyEnteringTrader, bytes) ← Alpha.decode 6 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  pure ({ transactTime, expireTime, quoteId, secondaryQuoteId, bidPx, bidSize, offerPx, offerSize, underlyingPx, underlyingDeltaPercentage, quoteRefPrice, partyIdExecutingTrader, negotiationId, quotingStatus, firmNegotiationId, partyExecutingFirm, partyExecutingTrader, partyEnteringTrader, pad2 }, bytes)

@[simp] theorem encode_length (message : SrqsQuoteEntryGrpComp) : (encode message).length = 136 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : SrqsQuoteEntryGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SrqsQuoteEntryGrpComp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end SrqsQuoteEntryGrpComp

/-- Srqs Quote Snapshot Notification -/
structure SrqsQuoteSnapshotNotification where
  pad2 : Alpha 2
  rbcHeaderComp : RbcHeaderComp
  messageEventSource : MessageEventSource
  pad6 : Alpha 6
  srqsQuoteEntryGrpComp : Bounded 1 SrqsQuoteEntryGrpComp
  deriving DecidableEq, Repr

namespace SrqsQuoteSnapshotNotification

def encode (message : SrqsQuoteSnapshotNotification) : List UInt8 :=
  Alpha.encode message.pad2
    ++ RbcHeaderComp.encode message.rbcHeaderComp
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.srqsQuoteEntryGrpComp.val.length)
    ++ MessageEventSource.encode message.messageEventSource
    ++ Alpha.encode message.pad6
    ++ encodeMany SrqsQuoteEntryGrpComp.encode message.srqsQuoteEntryGrpComp.val

def decode (bytes : List UInt8) : Option (SrqsQuoteSnapshotNotification × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderComp, bytes) ← RbcHeaderComp.decode bytes
  let (noQuoteEntries, bytes) ← decodeUInt 1 bytes
  let (messageEventSource, bytes) ← MessageEventSource.decode bytes
  let (pad6, bytes) ← Alpha.decode 6 bytes
  let (srqsQuoteEntryGrpComp_, bytes) ← decodeMany SrqsQuoteEntryGrpComp.decode noQuoteEntries.toNat bytes
  if fits_srqsQuoteEntryGrpComp : srqsQuoteEntryGrpComp_.length < 256 ^ 1 then
    pure ({ pad2, rbcHeaderComp, messageEventSource, pad6, srqsQuoteEntryGrpComp := ⟨srqsQuoteEntryGrpComp_, fits_srqsQuoteEntryGrpComp⟩ }, bytes)
  else none

theorem encode_length_pos (message : SrqsQuoteSnapshotNotification) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SrqsQuoteSnapshotNotification) : (encode message).length ≤ 34722 := by
  have bound_srqsQuoteEntryGrpComp := message.srqsQuoteEntryGrpComp.length_lt
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RbcHeaderComp.encode_length, encodeUInt_length, MessageEventSource.encode_length, encodeMany_length_const SrqsQuoteEntryGrpComp.encode 136 SrqsQuoteEntryGrpComp.encode_length]
  omega

@[simp] theorem decode_encode (message : SrqsQuoteSnapshotNotification) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [RbcHeaderComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [MessageEventSource.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 SrqsQuoteEntryGrpComp.encode SrqsQuoteEntryGrpComp.decode SrqsQuoteEntryGrpComp.decode_encode]
  simp only [Option.bind_some]
  simp only [message.srqsQuoteEntryGrpComp.length_lt, ↓reduceDIte]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : SrqsQuoteSnapshotNotification) : decode (encode message) = some (message, []) := by
  have trailing := decode_encode message []
  rw [List.append_nil] at trailing
  exact trailing

end SrqsQuoteSnapshotNotification

/-- Srqs Response: 26 bytes -/
structure SrqsResponse where
  pad2 : Alpha 2
  responseHeaderComp : ResponseHeaderComp
  deriving DecidableEq, Repr

namespace SrqsResponse

def encode (message : SrqsResponse) : List UInt8 :=
  Alpha.encode message.pad2
    ++ ResponseHeaderComp.encode message.responseHeaderComp

def decode (bytes : List UInt8) : Option (SrqsResponse × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (responseHeaderComp, bytes) ← ResponseHeaderComp.decode bytes
  pure ({ pad2, responseHeaderComp }, bytes)

@[simp] theorem encode_length (message : SrqsResponse) : (encode message).length = 26 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, ResponseHeaderComp.encode_length]

theorem encode_length_pos (message : SrqsResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SrqsResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [ResponseHeaderComp.decode_encode, Option.bind_some]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : SrqsResponse) : decode (encode message) = some (message, []) := by
  have trailing := decode_encode message []
  rw [List.append_nil] at trailing
  exact trailing

end SrqsResponse

/-- Srqs Status Broadcast: 42 bytes -/
structure SrqsStatusBroadcast where
  pad2 : Alpha 2
  rbcHeaderComp : RbcHeaderComp
  tradeDate : BitVec 32
  tradSesEvent : BitVec 8
  pad3 : Alpha 3
  deriving DecidableEq, Repr

namespace SrqsStatusBroadcast

def encode (message : SrqsStatusBroadcast) : List UInt8 :=
  Alpha.encode message.pad2
    ++ RbcHeaderComp.encode message.rbcHeaderComp
    ++ encodeUIntLE 4 message.tradeDate
    ++ encodeUInt 1 message.tradSesEvent
    ++ Alpha.encode message.pad3

def decode (bytes : List UInt8) : Option (SrqsStatusBroadcast × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderComp, bytes) ← RbcHeaderComp.decode bytes
  let (tradeDate, bytes) ← decodeUIntLE 4 bytes
  let (tradSesEvent, bytes) ← decodeUInt 1 bytes
  let (pad3, bytes) ← Alpha.decode 3 bytes
  pure ({ pad2, rbcHeaderComp, tradeDate, tradSesEvent, pad3 }, bytes)

@[simp] theorem encode_length (message : SrqsStatusBroadcast) : (encode message).length = 42 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RbcHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : SrqsStatusBroadcast) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SrqsStatusBroadcast) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [RbcHeaderComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : SrqsStatusBroadcast) : decode (encode message) = some (message, []) := by
  have trailing := decode_encode message []
  rw [List.append_nil] at trailing
  exact trailing

end SrqsStatusBroadcast

/-- Nrbc Header Comp: 16 bytes -/
structure NrbcHeaderComp where
  sendingTime : BitVec 64
  applSubId : BitVec 32
  applId : BitVec 8
  lastFragment : BitVec 8
  pad2 : Alpha 2
  deriving DecidableEq, Repr

namespace NrbcHeaderComp

def encode (message : NrbcHeaderComp) : List UInt8 :=
  encodeUIntLE 8 message.sendingTime
    ++ encodeUIntLE 4 message.applSubId
    ++ encodeUInt 1 message.applId
    ++ encodeUInt 1 message.lastFragment
    ++ Alpha.encode message.pad2

def decode (bytes : List UInt8) : Option (NrbcHeaderComp × List UInt8) := do
  let (sendingTime, bytes) ← decodeUIntLE 8 bytes
  let (applSubId, bytes) ← decodeUIntLE 4 bytes
  let (applId, bytes) ← decodeUInt 1 bytes
  let (lastFragment, bytes) ← decodeUInt 1 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  pure ({ sendingTime, applSubId, applId, lastFragment, pad2 }, bytes)

@[simp] theorem encode_length (message : NrbcHeaderComp) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : NrbcHeaderComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NrbcHeaderComp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end NrbcHeaderComp

/-- Service Availability Broadcast: 50 bytes -/
structure ServiceAvailabilityBroadcast where
  pad2 : Alpha 2
  nrbcHeaderComp : NrbcHeaderComp
  matchingEngineTradeDate : BitVec 32
  tradeManagerTradeDate : BitVec 32
  applSeqTradeDate : BitVec 32
  t7EntryServiceTradeDate : BitVec 32
  t7EntryServiceRtmTradeDate : BitVec 32
  partitionId : BitVec 16
  matchingEngineStatus : BitVec 8
  tradeManagerStatus : BitVec 8
  applSeqStatus : BitVec 8
  t7EntryServiceStatus : BitVec 8
  t7EntryServiceRtmStatus : BitVec 8
  pad5 : Alpha 5
  deriving DecidableEq, Repr

namespace ServiceAvailabilityBroadcast

def encode (message : ServiceAvailabilityBroadcast) : List UInt8 :=
  Alpha.encode message.pad2
    ++ NrbcHeaderComp.encode message.nrbcHeaderComp
    ++ encodeUIntLE 4 message.matchingEngineTradeDate
    ++ encodeUIntLE 4 message.tradeManagerTradeDate
    ++ encodeUIntLE 4 message.applSeqTradeDate
    ++ encodeUIntLE 4 message.t7EntryServiceTradeDate
    ++ encodeUIntLE 4 message.t7EntryServiceRtmTradeDate
    ++ encodeUIntLE 2 message.partitionId
    ++ encodeUInt 1 message.matchingEngineStatus
    ++ encodeUInt 1 message.tradeManagerStatus
    ++ encodeUInt 1 message.applSeqStatus
    ++ encodeUInt 1 message.t7EntryServiceStatus
    ++ encodeUInt 1 message.t7EntryServiceRtmStatus
    ++ Alpha.encode message.pad5

def decode (bytes : List UInt8) : Option (ServiceAvailabilityBroadcast × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (nrbcHeaderComp, bytes) ← NrbcHeaderComp.decode bytes
  let (matchingEngineTradeDate, bytes) ← decodeUIntLE 4 bytes
  let (tradeManagerTradeDate, bytes) ← decodeUIntLE 4 bytes
  let (applSeqTradeDate, bytes) ← decodeUIntLE 4 bytes
  let (t7EntryServiceTradeDate, bytes) ← decodeUIntLE 4 bytes
  let (t7EntryServiceRtmTradeDate, bytes) ← decodeUIntLE 4 bytes
  let (partitionId, bytes) ← decodeUIntLE 2 bytes
  let (matchingEngineStatus, bytes) ← decodeUInt 1 bytes
  let (tradeManagerStatus, bytes) ← decodeUInt 1 bytes
  let (applSeqStatus, bytes) ← decodeUInt 1 bytes
  let (t7EntryServiceStatus, bytes) ← decodeUInt 1 bytes
  let (t7EntryServiceRtmStatus, bytes) ← decodeUInt 1 bytes
  let (pad5, bytes) ← Alpha.decode 5 bytes
  pure ({ pad2, nrbcHeaderComp, matchingEngineTradeDate, tradeManagerTradeDate, applSeqTradeDate, t7EntryServiceTradeDate, t7EntryServiceRtmTradeDate, partitionId, matchingEngineStatus, tradeManagerStatus, applSeqStatus, t7EntryServiceStatus, t7EntryServiceRtmStatus, pad5 }, bytes)

@[simp] theorem encode_length (message : ServiceAvailabilityBroadcast) : (encode message).length = 50 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, NrbcHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : ServiceAvailabilityBroadcast) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ServiceAvailabilityBroadcast) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [NrbcHeaderComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : ServiceAvailabilityBroadcast) : decode (encode message) = some (message, []) := by
  have trailing := decode_encode message []
  rw [List.append_nil] at trailing
  exact trailing

end ServiceAvailabilityBroadcast

/-- Service Availability Market Broadcast: 26 bytes -/
structure ServiceAvailabilityMarketBroadcast where
  pad2 : Alpha 2
  nrbcHeaderComp : NrbcHeaderComp
  selectiveRequestForQuoteServiceTradeDate : BitVec 32
  selectiveRequestForQuoteServiceStatus : BitVec 8
  selectiveRequestForQuoteRtmServiceStatus : BitVec 8
  newsRtmServiceStatus : BitVec 8
  riskControlRtmServiceStatus : BitVec 8
  deriving DecidableEq, Repr

namespace ServiceAvailabilityMarketBroadcast

def encode (message : ServiceAvailabilityMarketBroadcast) : List UInt8 :=
  Alpha.encode message.pad2
    ++ NrbcHeaderComp.encode message.nrbcHeaderComp
    ++ encodeUIntLE 4 message.selectiveRequestForQuoteServiceTradeDate
    ++ encodeUInt 1 message.selectiveRequestForQuoteServiceStatus
    ++ encodeUInt 1 message.selectiveRequestForQuoteRtmServiceStatus
    ++ encodeUInt 1 message.newsRtmServiceStatus
    ++ encodeUInt 1 message.riskControlRtmServiceStatus

def decode (bytes : List UInt8) : Option (ServiceAvailabilityMarketBroadcast × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (nrbcHeaderComp, bytes) ← NrbcHeaderComp.decode bytes
  let (selectiveRequestForQuoteServiceTradeDate, bytes) ← decodeUIntLE 4 bytes
  let (selectiveRequestForQuoteServiceStatus, bytes) ← decodeUInt 1 bytes
  let (selectiveRequestForQuoteRtmServiceStatus, bytes) ← decodeUInt 1 bytes
  let (newsRtmServiceStatus, bytes) ← decodeUInt 1 bytes
  let (riskControlRtmServiceStatus, bytes) ← decodeUInt 1 bytes
  pure ({ pad2, nrbcHeaderComp, selectiveRequestForQuoteServiceTradeDate, selectiveRequestForQuoteServiceStatus, selectiveRequestForQuoteRtmServiceStatus, newsRtmServiceStatus, riskControlRtmServiceStatus }, bytes)

@[simp] theorem encode_length (message : ServiceAvailabilityMarketBroadcast) : (encode message).length = 26 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, NrbcHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : ServiceAvailabilityMarketBroadcast) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ServiceAvailabilityMarketBroadcast) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [NrbcHeaderComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt, Option.bind_some]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : ServiceAvailabilityMarketBroadcast) : decode (encode message) = some (message, []) := by
  have trailing := decode_encode message []
  rw [List.append_nil] at trailing
  exact trailing

end ServiceAvailabilityMarketBroadcast

/-- Status Broadcast: 42 bytes -/
structure StatusBroadcast where
  pad2 : Alpha 2
  rbcHeaderComp : RbcHeaderComp
  tradeDate : BitVec 32
  tradSesEvent : BitVec 8
  pad3 : Alpha 3
  deriving DecidableEq, Repr

namespace StatusBroadcast

def encode (message : StatusBroadcast) : List UInt8 :=
  Alpha.encode message.pad2
    ++ RbcHeaderComp.encode message.rbcHeaderComp
    ++ encodeUIntLE 4 message.tradeDate
    ++ encodeUInt 1 message.tradSesEvent
    ++ Alpha.encode message.pad3

def decode (bytes : List UInt8) : Option (StatusBroadcast × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderComp, bytes) ← RbcHeaderComp.decode bytes
  let (tradeDate, bytes) ← decodeUIntLE 4 bytes
  let (tradSesEvent, bytes) ← decodeUInt 1 bytes
  let (pad3, bytes) ← Alpha.decode 3 bytes
  pure ({ pad2, rbcHeaderComp, tradeDate, tradSesEvent, pad3 }, bytes)

@[simp] theorem encode_length (message : StatusBroadcast) : (encode message).length = 42 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RbcHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : StatusBroadcast) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StatusBroadcast) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [RbcHeaderComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : StatusBroadcast) : decode (encode message) = some (message, []) := by
  have trailing := decode_encode message []
  rw [List.append_nil] at trailing
  exact trailing

end StatusBroadcast

/-- Subscribe Response: 34 bytes -/
structure SubscribeResponse where
  pad2 : Alpha 2
  responseHeaderComp : ResponseHeaderComp
  applSubId : BitVec 32
  pad4 : Alpha 4
  deriving DecidableEq, Repr

namespace SubscribeResponse

def encode (message : SubscribeResponse) : List UInt8 :=
  Alpha.encode message.pad2
    ++ ResponseHeaderComp.encode message.responseHeaderComp
    ++ encodeUIntLE 4 message.applSubId
    ++ Alpha.encode message.pad4

def decode (bytes : List UInt8) : Option (SubscribeResponse × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (responseHeaderComp, bytes) ← ResponseHeaderComp.decode bytes
  let (applSubId, bytes) ← decodeUIntLE 4 bytes
  let (pad4, bytes) ← Alpha.decode 4 bytes
  pure ({ pad2, responseHeaderComp, applSubId, pad4 }, bytes)

@[simp] theorem encode_length (message : SubscribeResponse) : (encode message).length = 34 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, ResponseHeaderComp.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : SubscribeResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SubscribeResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [ResponseHeaderComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : SubscribeResponse) : decode (encode message) = some (message, []) := by
  have trailing := decode_encode message []
  rw [List.append_nil] at trailing
  exact trailing

end SubscribeResponse

/-- Trd Instrmnt Leg Grp Comp: 24 bytes -/
structure TrdInstrmntLegGrpComp where
  legSecurityId : BitVec 64
  legPrice : BitVec 64
  legQty : BitVec 64
  deriving DecidableEq, Repr

namespace TrdInstrmntLegGrpComp

def encode (message : TrdInstrmntLegGrpComp) : List UInt8 :=
  encodeUIntLE 8 message.legSecurityId
    ++ encodeUIntLE 8 message.legPrice
    ++ encodeUIntLE 8 message.legQty

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
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
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
    ++ encodeUInt 1 message.eventType
    ++ Alpha.encode message.pad3

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
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
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
    ++ Alpha.encode message.instrAttribValue
    ++ Alpha.encode message.pad7

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
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
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
    ++ Alpha.encode message.underlyingStipType
    ++ Alpha.encode message.pad1

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
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end UnderlyingStipGrpComp

/-- Tes Approve Broadcast -/
structure TesApproveBroadcast where
  pad2 : Alpha 2
  rbcHeaderComp : RbcHeaderComp
  securityId : BitVec 64
  lastPx : BitVec 64
  allocQty : BitVec 64
  transactTime : BitVec 64
  underlyingPx : BitVec 64
  transBkdTime : BitVec 64
  relatedClosePrice : BitVec 64
  relatedTradeQuantity : BitVec 64
  relatedSecurityId : BitVec 64
  relatedPx : BitVec 64
  underlyingQty : BitVec 64
  marketSegmentId : BitVec 32
  packageId : BitVec 32
  tesExecId : BitVec 32
  allocId : BitVec 32
  underlyingSettlementDate : BitVec 32
  underlyingMaturityDate : BitVec 32
  relatedTradeId : BitVec 32
  relatedMarketSegmentId : BitVec 32
  negotiationId : BitVec 32
  tesEnrichmentRuleId : BitVec 32
  autoApprovalRuleId : BitVec 32
  trdType : BitVec 16
  side : BitVec 8
  tradePublishIndicator : BitVec 8
  productComplex : BitVec 8
  tradeReportType : BitVec 8
  trdRptStatus : BitVec 8
  tradingCapacity : BitVec 8
  partyIdSettlementLocation : BitVec 8
  tradeAllocStatus : BitVec 8
  hedgeType : BitVec 8
  messageEventSource : MessageEventSource
  tradeReportId : Alpha 20
  partyExecutingFirm : Alpha 5
  partyExecutingTrader : Alpha 6
  partyIdEnteringFirm : BitVec 8
  partyEnteringTrader : Alpha 6
  positionEffect : PositionEffect
  rootPartyExecutingFirm : Alpha 5
  rootPartyExecutingTrader : Alpha 6
  freeText1 : Alpha 12
  freeText2 : Alpha 12
  freeText3 : Alpha 12
  partyIdTakeUpTradingFirm : Alpha 5
  account : Alpha 2
  partyIdPositionAccount : Alpha 32
  partyIdOrderOriginationFirm : Alpha 7
  partyIdBeneficiary : Alpha 9
  partyIdLocationId : Alpha 2
  custOrderHandlingInst : CustOrderHandlingInst
  complianceText : Alpha 20
  underlyingSecurityId : Alpha 12
  underlyingSecurityDesc : Alpha 30
  underlyingCurrency : Alpha 3
  underlyingIssuer : Alpha 30
  pad3 : Alpha 3
  trdInstrmntLegGrpComp : Bounded 1 TrdInstrmntLegGrpComp
  instrumentEventGrpComp : Bounded 1 InstrumentEventGrpComp
  instrumentAttributeGrpComp : Bounded 1 InstrumentAttributeGrpComp
  underlyingStipGrpComp : Bounded 1 UnderlyingStipGrpComp
  varText : Bounded 2 UInt8
  alignmentPadding : Capped 4282374239
  deriving DecidableEq, Repr

namespace TesApproveBroadcast

def encode (message : TesApproveBroadcast) : List UInt8 :=
  Alpha.encode message.pad2
    ++ RbcHeaderComp.encode message.rbcHeaderComp
    ++ encodeUIntLE 8 message.securityId
    ++ encodeUIntLE 8 message.lastPx
    ++ encodeUIntLE 8 message.allocQty
    ++ encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 8 message.underlyingPx
    ++ encodeUIntLE 8 message.transBkdTime
    ++ encodeUIntLE 8 message.relatedClosePrice
    ++ encodeUIntLE 8 message.relatedTradeQuantity
    ++ encodeUIntLE 8 message.relatedSecurityId
    ++ encodeUIntLE 8 message.relatedPx
    ++ encodeUIntLE 8 message.underlyingQty
    ++ encodeUIntLE 4 message.marketSegmentId
    ++ encodeUIntLE 4 message.packageId
    ++ encodeUIntLE 4 message.tesExecId
    ++ encodeUIntLE 4 message.allocId
    ++ encodeUIntLE 4 message.underlyingSettlementDate
    ++ encodeUIntLE 4 message.underlyingMaturityDate
    ++ encodeUIntLE 4 message.relatedTradeId
    ++ encodeUIntLE 4 message.relatedMarketSegmentId
    ++ encodeUIntLE 4 message.negotiationId
    ++ encodeUIntLE 4 message.tesEnrichmentRuleId
    ++ encodeUIntLE 4 message.autoApprovalRuleId
    ++ encodeUIntLE 2 message.trdType
    ++ encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.varText.val.length)
    ++ encodeUInt 1 message.side
    ++ encodeUInt 1 message.tradePublishIndicator
    ++ encodeUInt 1 message.productComplex
    ++ encodeUInt 1 message.tradeReportType
    ++ encodeUInt 1 message.trdRptStatus
    ++ encodeUInt 1 message.tradingCapacity
    ++ encodeUInt 1 message.partyIdSettlementLocation
    ++ encodeUInt 1 message.tradeAllocStatus
    ++ encodeUInt 1 message.hedgeType
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.trdInstrmntLegGrpComp.val.length)
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.instrumentEventGrpComp.val.length)
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.instrumentAttributeGrpComp.val.length)
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.underlyingStipGrpComp.val.length)
    ++ MessageEventSource.encode message.messageEventSource
    ++ Alpha.encode message.tradeReportId
    ++ Alpha.encode message.partyExecutingFirm
    ++ Alpha.encode message.partyExecutingTrader
    ++ encodeUInt 1 message.partyIdEnteringFirm
    ++ Alpha.encode message.partyEnteringTrader
    ++ PositionEffect.encode message.positionEffect
    ++ Alpha.encode message.rootPartyExecutingFirm
    ++ Alpha.encode message.rootPartyExecutingTrader
    ++ Alpha.encode message.freeText1
    ++ Alpha.encode message.freeText2
    ++ Alpha.encode message.freeText3
    ++ Alpha.encode message.partyIdTakeUpTradingFirm
    ++ Alpha.encode message.account
    ++ Alpha.encode message.partyIdPositionAccount
    ++ Alpha.encode message.partyIdOrderOriginationFirm
    ++ Alpha.encode message.partyIdBeneficiary
    ++ Alpha.encode message.partyIdLocationId
    ++ CustOrderHandlingInst.encode message.custOrderHandlingInst
    ++ Alpha.encode message.complianceText
    ++ Alpha.encode message.underlyingSecurityId
    ++ Alpha.encode message.underlyingSecurityDesc
    ++ Alpha.encode message.underlyingCurrency
    ++ Alpha.encode message.underlyingIssuer
    ++ Alpha.encode message.pad3
    ++ encodeMany TrdInstrmntLegGrpComp.encode message.trdInstrmntLegGrpComp.val
    ++ encodeMany InstrumentEventGrpComp.encode message.instrumentEventGrpComp.val
    ++ encodeMany InstrumentAttributeGrpComp.encode message.instrumentAttributeGrpComp.val
    ++ encodeMany UnderlyingStipGrpComp.encode message.underlyingStipGrpComp.val
    ++ encodeMany Byte.encode message.varText.val
    ++ message.alignmentPadding.val

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option TesApproveBroadcast := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderComp, bytes) ← RbcHeaderComp.decode bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  let (allocQty, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (underlyingPx, bytes) ← decodeUIntLE 8 bytes
  let (transBkdTime, bytes) ← decodeUIntLE 8 bytes
  let (relatedClosePrice, bytes) ← decodeUIntLE 8 bytes
  let (relatedTradeQuantity, bytes) ← decodeUIntLE 8 bytes
  let (relatedSecurityId, bytes) ← decodeUIntLE 8 bytes
  let (relatedPx, bytes) ← decodeUIntLE 8 bytes
  let (underlyingQty, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (packageId, bytes) ← decodeUIntLE 4 bytes
  let (tesExecId, bytes) ← decodeUIntLE 4 bytes
  let (allocId, bytes) ← decodeUIntLE 4 bytes
  let (underlyingSettlementDate, bytes) ← decodeUIntLE 4 bytes
  let (underlyingMaturityDate, bytes) ← decodeUIntLE 4 bytes
  let (relatedTradeId, bytes) ← decodeUIntLE 4 bytes
  let (relatedMarketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (negotiationId, bytes) ← decodeUIntLE 4 bytes
  let (tesEnrichmentRuleId, bytes) ← decodeUIntLE 4 bytes
  let (autoApprovalRuleId, bytes) ← decodeUIntLE 4 bytes
  let (trdType, bytes) ← decodeUIntLE 2 bytes
  let (varTextLen, bytes) ← decodeUIntLE 2 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (tradePublishIndicator, bytes) ← decodeUInt 1 bytes
  let (productComplex, bytes) ← decodeUInt 1 bytes
  let (tradeReportType, bytes) ← decodeUInt 1 bytes
  let (trdRptStatus, bytes) ← decodeUInt 1 bytes
  let (tradingCapacity, bytes) ← decodeUInt 1 bytes
  let (partyIdSettlementLocation, bytes) ← decodeUInt 1 bytes
  let (tradeAllocStatus, bytes) ← decodeUInt 1 bytes
  let (hedgeType, bytes) ← decodeUInt 1 bytes
  let (noLegs, bytes) ← decodeUInt 1 bytes
  let (noEvents, bytes) ← decodeUInt 1 bytes
  let (noInstrAttrib, bytes) ← decodeUInt 1 bytes
  let (noUnderlyingStips, bytes) ← decodeUInt 1 bytes
  let (messageEventSource, bytes) ← MessageEventSource.decode bytes
  let (tradeReportId, bytes) ← Alpha.decode 20 bytes
  let (partyExecutingFirm, bytes) ← Alpha.decode 5 bytes
  let (partyExecutingTrader, bytes) ← Alpha.decode 6 bytes
  let (partyIdEnteringFirm, bytes) ← decodeUInt 1 bytes
  let (partyEnteringTrader, bytes) ← Alpha.decode 6 bytes
  let (positionEffect, bytes) ← PositionEffect.decode bytes
  let (rootPartyExecutingFirm, bytes) ← Alpha.decode 5 bytes
  let (rootPartyExecutingTrader, bytes) ← Alpha.decode 6 bytes
  let (freeText1, bytes) ← Alpha.decode 12 bytes
  let (freeText2, bytes) ← Alpha.decode 12 bytes
  let (freeText3, bytes) ← Alpha.decode 12 bytes
  let (partyIdTakeUpTradingFirm, bytes) ← Alpha.decode 5 bytes
  let (account, bytes) ← Alpha.decode 2 bytes
  let (partyIdPositionAccount, bytes) ← Alpha.decode 32 bytes
  let (partyIdOrderOriginationFirm, bytes) ← Alpha.decode 7 bytes
  let (partyIdBeneficiary, bytes) ← Alpha.decode 9 bytes
  let (partyIdLocationId, bytes) ← Alpha.decode 2 bytes
  let (custOrderHandlingInst, bytes) ← CustOrderHandlingInst.decode bytes
  let (complianceText, bytes) ← Alpha.decode 20 bytes
  let (underlyingSecurityId, bytes) ← Alpha.decode 12 bytes
  let (underlyingSecurityDesc, bytes) ← Alpha.decode 30 bytes
  let (underlyingCurrency, bytes) ← Alpha.decode 3 bytes
  let (underlyingIssuer, bytes) ← Alpha.decode 30 bytes
  let (pad3, bytes) ← Alpha.decode 3 bytes
  let (trdInstrmntLegGrpComp_, bytes) ← decodeMany TrdInstrmntLegGrpComp.decode noLegs.toNat bytes
  let (instrumentEventGrpComp_, bytes) ← decodeMany InstrumentEventGrpComp.decode noEvents.toNat bytes
  let (instrumentAttributeGrpComp_, bytes) ← decodeMany InstrumentAttributeGrpComp.decode noInstrAttrib.toNat bytes
  let (underlyingStipGrpComp_, bytes) ← decodeMany UnderlyingStipGrpComp.decode noUnderlyingStips.toNat bytes
  let (varText_, bytes) ← decodeMany Byte.decode varTextLen.toNat bytes
  let alignmentPadding_ := bytes
  if fits_trdInstrmntLegGrpComp : trdInstrmntLegGrpComp_.length < 256 ^ 1 then
    if fits_instrumentEventGrpComp : instrumentEventGrpComp_.length < 256 ^ 1 then
      if fits_instrumentAttributeGrpComp : instrumentAttributeGrpComp_.length < 256 ^ 1 then
        if fits_underlyingStipGrpComp : underlyingStipGrpComp_.length < 256 ^ 1 then
          if fits_varText : varText_.length < 256 ^ 2 then
            if fits_alignmentPadding : alignmentPadding_.length ≤ 4282374239 then
              pure { pad2, rbcHeaderComp, securityId, lastPx, allocQty, transactTime, underlyingPx, transBkdTime, relatedClosePrice, relatedTradeQuantity, relatedSecurityId, relatedPx, underlyingQty, marketSegmentId, packageId, tesExecId, allocId, underlyingSettlementDate, underlyingMaturityDate, relatedTradeId, relatedMarketSegmentId, negotiationId, tesEnrichmentRuleId, autoApprovalRuleId, trdType, side, tradePublishIndicator, productComplex, tradeReportType, trdRptStatus, tradingCapacity, partyIdSettlementLocation, tradeAllocStatus, hedgeType, messageEventSource, tradeReportId, partyExecutingFirm, partyExecutingTrader, partyIdEnteringFirm, partyEnteringTrader, positionEffect, rootPartyExecutingFirm, rootPartyExecutingTrader, freeText1, freeText2, freeText3, partyIdTakeUpTradingFirm, account, partyIdPositionAccount, partyIdOrderOriginationFirm, partyIdBeneficiary, partyIdLocationId, custOrderHandlingInst, complianceText, underlyingSecurityId, underlyingSecurityDesc, underlyingCurrency, underlyingIssuer, pad3, trdInstrmntLegGrpComp := ⟨trdInstrmntLegGrpComp_, fits_trdInstrmntLegGrpComp⟩, instrumentEventGrpComp := ⟨instrumentEventGrpComp_, fits_instrumentEventGrpComp⟩, instrumentAttributeGrpComp := ⟨instrumentAttributeGrpComp_, fits_instrumentAttributeGrpComp⟩, underlyingStipGrpComp := ⟨underlyingStipGrpComp_, fits_underlyingStipGrpComp⟩, varText := ⟨varText_, fits_varText⟩, alignmentPadding := ⟨alignmentPadding_, fits_alignmentPadding⟩ }
            else none
          else none
        else none
      else none
    else none
  else none

theorem encode_length_pos (message : TesApproveBroadcast) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : TesApproveBroadcast) : (encode message).length ≤ 4282468760 := by
  have bound_trdInstrmntLegGrpComp := message.trdInstrmntLegGrpComp.length_lt
  have bound_instrumentEventGrpComp := message.instrumentEventGrpComp.length_lt
  have bound_instrumentAttributeGrpComp := message.instrumentAttributeGrpComp.length_lt
  have bound_underlyingStipGrpComp := message.underlyingStipGrpComp.length_lt
  have bound_varText := message.varText.length_lt
  have bound_alignmentPadding := message.alignmentPadding.length_le
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RbcHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length, MessageEventSource.encode_length, PositionEffect.encode_length, CustOrderHandlingInst.encode_length, encodeMany_length_const TrdInstrmntLegGrpComp.encode 24 TrdInstrmntLegGrpComp.encode_length, encodeMany_length_const InstrumentEventGrpComp.encode 8 InstrumentEventGrpComp.encode_length, encodeMany_length_const InstrumentAttributeGrpComp.encode 40 InstrumentAttributeGrpComp.encode_length, encodeMany_length_const UnderlyingStipGrpComp.encode 40 UnderlyingStipGrpComp.encode_length, encodeMany_length_const Byte.encode 1 Byte.encode_length]
  omega

theorem decode_encode (message : TesApproveBroadcast) : decode (encode message) = some message := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [RbcHeaderComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [MessageEventSource.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [PositionEffect.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [CustOrderHandlingInst.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 TrdInstrmntLegGrpComp.encode TrdInstrmntLegGrpComp.decode TrdInstrmntLegGrpComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 InstrumentEventGrpComp.encode InstrumentEventGrpComp.decode InstrumentEventGrpComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 InstrumentAttributeGrpComp.encode InstrumentAttributeGrpComp.decode InstrumentAttributeGrpComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 UnderlyingStipGrpComp.encode UnderlyingStipGrpComp.decode UnderlyingStipGrpComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 2 Byte.encode Byte.decode Byte.decode_encode]
  simp only [Option.bind_some]
  simp only [message.trdInstrmntLegGrpComp.length_lt, message.instrumentEventGrpComp.length_lt, message.instrumentAttributeGrpComp.length_lt, message.underlyingStipGrpComp.length_lt, message.varText.length_lt, message.alignmentPadding.length_le, ↓reduceDIte]
  rfl

end TesApproveBroadcast

/-- Side Alloc Grp Bc Comp: 40 bytes -/
structure SideAllocGrpBcComp where
  allocQty : BitVec 64
  reversalApprovalTime : BitVec 64
  individualAllocId : BitVec 32
  tesEnrichmentRuleId : BitVec 32
  partyExecutingFirm : Alpha 5
  partyExecutingTrader : Alpha 6
  side : BitVec 8
  tradeAllocStatus : BitVec 8
  pad3 : Alpha 3
  deriving DecidableEq, Repr

namespace SideAllocGrpBcComp

def encode (message : SideAllocGrpBcComp) : List UInt8 :=
  encodeUIntLE 8 message.allocQty
    ++ encodeUIntLE 8 message.reversalApprovalTime
    ++ encodeUIntLE 4 message.individualAllocId
    ++ encodeUIntLE 4 message.tesEnrichmentRuleId
    ++ Alpha.encode message.partyExecutingFirm
    ++ Alpha.encode message.partyExecutingTrader
    ++ encodeUInt 1 message.side
    ++ encodeUInt 1 message.tradeAllocStatus
    ++ Alpha.encode message.pad3

def decode (bytes : List UInt8) : Option (SideAllocGrpBcComp × List UInt8) := do
  let (allocQty, bytes) ← decodeUIntLE 8 bytes
  let (reversalApprovalTime, bytes) ← decodeUIntLE 8 bytes
  let (individualAllocId, bytes) ← decodeUIntLE 4 bytes
  let (tesEnrichmentRuleId, bytes) ← decodeUIntLE 4 bytes
  let (partyExecutingFirm, bytes) ← Alpha.decode 5 bytes
  let (partyExecutingTrader, bytes) ← Alpha.decode 6 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (tradeAllocStatus, bytes) ← decodeUInt 1 bytes
  let (pad3, bytes) ← Alpha.decode 3 bytes
  pure ({ allocQty, reversalApprovalTime, individualAllocId, tesEnrichmentRuleId, partyExecutingFirm, partyExecutingTrader, side, tradeAllocStatus, pad3 }, bytes)

@[simp] theorem encode_length (message : SideAllocGrpBcComp) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : SideAllocGrpBcComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SideAllocGrpBcComp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end SideAllocGrpBcComp

/-- Trd Clearing Price Leg Grp Comp: 16 bytes -/
structure TrdClearingPriceLegGrpComp where
  legSecurityId : BitVec 64
  legClearingTradePrice : BitVec 64
  deriving DecidableEq, Repr

namespace TrdClearingPriceLegGrpComp

def encode (message : TrdClearingPriceLegGrpComp) : List UInt8 :=
  encodeUIntLE 8 message.legSecurityId
    ++ encodeUIntLE 8 message.legClearingTradePrice

def decode (bytes : List UInt8) : Option (TrdClearingPriceLegGrpComp × List UInt8) := do
  let (legSecurityId, bytes) ← decodeUIntLE 8 bytes
  let (legClearingTradePrice, bytes) ← decodeUIntLE 8 bytes
  pure ({ legSecurityId, legClearingTradePrice }, bytes)

@[simp] theorem encode_length (message : TrdClearingPriceLegGrpComp) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : TrdClearingPriceLegGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TrdClearingPriceLegGrpComp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

end TrdClearingPriceLegGrpComp

/-- Tes Broadcast -/
structure TesBroadcast where
  pad2 : Alpha 2
  rbcHeaderComp : RbcHeaderComp
  securityId : BitVec 64
  lastPx : BitVec 64
  transactTime : BitVec 64
  underlyingPx : BitVec 64
  transBkdTime : BitVec 64
  relatedClosePrice : BitVec 64
  relatedTradeQuantity : BitVec 64
  relatedSecurityId : BitVec 64
  relatedPx : BitVec 64
  underlyingQty : BitVec 64
  marketSegmentId : BitVec 32
  packageId : BitVec 32
  tesExecId : BitVec 32
  underlyingSettlementDate : BitVec 32
  underlyingMaturityDate : BitVec 32
  relatedTradeId : BitVec 32
  relatedMarketSegmentId : BitVec 32
  autoApprovalRuleId : BitVec 32
  trdType : BitVec 16
  tradeReportType : BitVec 8
  trdRptStatus : BitVec 8
  productComplex : BitVec 8
  tradePublishIndicator : BitVec 8
  partyIdSettlementLocation : BitVec 8
  hedgeType : BitVec 8
  swapClearer : BitVec 8
  messageEventSource : MessageEventSource
  tradeReportText : Alpha 20
  tradeReportId : Alpha 20
  rootPartyExecutingFirm : Alpha 5
  rootPartyExecutingTrader : Alpha 6
  underlyingSecurityId : Alpha 12
  underlyingSecurityDesc : Alpha 30
  underlyingCurrency : Alpha 3
  underlyingIssuer : Alpha 30
  sideAllocGrpBcComp : Bounded 1 SideAllocGrpBcComp
  trdInstrmntLegGrpComp : Bounded 1 TrdInstrmntLegGrpComp
  instrumentEventGrpComp : Bounded 1 InstrumentEventGrpComp
  trdClearingPriceLegGrpComp : Bounded 1 TrdClearingPriceLegGrpComp
  instrumentAttributeGrpComp : Bounded 1 InstrumentAttributeGrpComp
  underlyingStipGrpComp : Bounded 1 UnderlyingStipGrpComp
  varText : Bounded 2 UInt8
  alignmentPadding : Capped 4282374239
  deriving DecidableEq, Repr

namespace TesBroadcast

def encode (message : TesBroadcast) : List UInt8 :=
  Alpha.encode message.pad2
    ++ RbcHeaderComp.encode message.rbcHeaderComp
    ++ encodeUIntLE 8 message.securityId
    ++ encodeUIntLE 8 message.lastPx
    ++ encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 8 message.underlyingPx
    ++ encodeUIntLE 8 message.transBkdTime
    ++ encodeUIntLE 8 message.relatedClosePrice
    ++ encodeUIntLE 8 message.relatedTradeQuantity
    ++ encodeUIntLE 8 message.relatedSecurityId
    ++ encodeUIntLE 8 message.relatedPx
    ++ encodeUIntLE 8 message.underlyingQty
    ++ encodeUIntLE 4 message.marketSegmentId
    ++ encodeUIntLE 4 message.packageId
    ++ encodeUIntLE 4 message.tesExecId
    ++ encodeUIntLE 4 message.underlyingSettlementDate
    ++ encodeUIntLE 4 message.underlyingMaturityDate
    ++ encodeUIntLE 4 message.relatedTradeId
    ++ encodeUIntLE 4 message.relatedMarketSegmentId
    ++ encodeUIntLE 4 message.autoApprovalRuleId
    ++ encodeUIntLE 2 message.trdType
    ++ encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.varText.val.length)
    ++ encodeUInt 1 message.tradeReportType
    ++ encodeUInt 1 message.trdRptStatus
    ++ encodeUInt 1 message.productComplex
    ++ encodeUInt 1 message.tradePublishIndicator
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.instrumentEventGrpComp.val.length)
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.instrumentAttributeGrpComp.val.length)
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.underlyingStipGrpComp.val.length)
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.sideAllocGrpBcComp.val.length)
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.trdInstrmntLegGrpComp.val.length)
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.trdClearingPriceLegGrpComp.val.length)
    ++ encodeUInt 1 message.partyIdSettlementLocation
    ++ encodeUInt 1 message.hedgeType
    ++ encodeUInt 1 message.swapClearer
    ++ MessageEventSource.encode message.messageEventSource
    ++ Alpha.encode message.tradeReportText
    ++ Alpha.encode message.tradeReportId
    ++ Alpha.encode message.rootPartyExecutingFirm
    ++ Alpha.encode message.rootPartyExecutingTrader
    ++ Alpha.encode message.underlyingSecurityId
    ++ Alpha.encode message.underlyingSecurityDesc
    ++ Alpha.encode message.underlyingCurrency
    ++ Alpha.encode message.underlyingIssuer
    ++ encodeMany SideAllocGrpBcComp.encode message.sideAllocGrpBcComp.val
    ++ encodeMany TrdInstrmntLegGrpComp.encode message.trdInstrmntLegGrpComp.val
    ++ encodeMany InstrumentEventGrpComp.encode message.instrumentEventGrpComp.val
    ++ encodeMany TrdClearingPriceLegGrpComp.encode message.trdClearingPriceLegGrpComp.val
    ++ encodeMany InstrumentAttributeGrpComp.encode message.instrumentAttributeGrpComp.val
    ++ encodeMany UnderlyingStipGrpComp.encode message.underlyingStipGrpComp.val
    ++ encodeMany Byte.encode message.varText.val
    ++ message.alignmentPadding.val

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option TesBroadcast := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderComp, bytes) ← RbcHeaderComp.decode bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (underlyingPx, bytes) ← decodeUIntLE 8 bytes
  let (transBkdTime, bytes) ← decodeUIntLE 8 bytes
  let (relatedClosePrice, bytes) ← decodeUIntLE 8 bytes
  let (relatedTradeQuantity, bytes) ← decodeUIntLE 8 bytes
  let (relatedSecurityId, bytes) ← decodeUIntLE 8 bytes
  let (relatedPx, bytes) ← decodeUIntLE 8 bytes
  let (underlyingQty, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (packageId, bytes) ← decodeUIntLE 4 bytes
  let (tesExecId, bytes) ← decodeUIntLE 4 bytes
  let (underlyingSettlementDate, bytes) ← decodeUIntLE 4 bytes
  let (underlyingMaturityDate, bytes) ← decodeUIntLE 4 bytes
  let (relatedTradeId, bytes) ← decodeUIntLE 4 bytes
  let (relatedMarketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (autoApprovalRuleId, bytes) ← decodeUIntLE 4 bytes
  let (trdType, bytes) ← decodeUIntLE 2 bytes
  let (varTextLen, bytes) ← decodeUIntLE 2 bytes
  let (tradeReportType, bytes) ← decodeUInt 1 bytes
  let (trdRptStatus, bytes) ← decodeUInt 1 bytes
  let (productComplex, bytes) ← decodeUInt 1 bytes
  let (tradePublishIndicator, bytes) ← decodeUInt 1 bytes
  let (noEvents, bytes) ← decodeUInt 1 bytes
  let (noInstrAttrib, bytes) ← decodeUInt 1 bytes
  let (noUnderlyingStips, bytes) ← decodeUInt 1 bytes
  let (noSideAllocs, bytes) ← decodeUInt 1 bytes
  let (noLegs, bytes) ← decodeUInt 1 bytes
  let (noLegClearingPrices, bytes) ← decodeUInt 1 bytes
  let (partyIdSettlementLocation, bytes) ← decodeUInt 1 bytes
  let (hedgeType, bytes) ← decodeUInt 1 bytes
  let (swapClearer, bytes) ← decodeUInt 1 bytes
  let (messageEventSource, bytes) ← MessageEventSource.decode bytes
  let (tradeReportText, bytes) ← Alpha.decode 20 bytes
  let (tradeReportId, bytes) ← Alpha.decode 20 bytes
  let (rootPartyExecutingFirm, bytes) ← Alpha.decode 5 bytes
  let (rootPartyExecutingTrader, bytes) ← Alpha.decode 6 bytes
  let (underlyingSecurityId, bytes) ← Alpha.decode 12 bytes
  let (underlyingSecurityDesc, bytes) ← Alpha.decode 30 bytes
  let (underlyingCurrency, bytes) ← Alpha.decode 3 bytes
  let (underlyingIssuer, bytes) ← Alpha.decode 30 bytes
  let (sideAllocGrpBcComp_, bytes) ← decodeMany SideAllocGrpBcComp.decode noSideAllocs.toNat bytes
  let (trdInstrmntLegGrpComp_, bytes) ← decodeMany TrdInstrmntLegGrpComp.decode noLegs.toNat bytes
  let (instrumentEventGrpComp_, bytes) ← decodeMany InstrumentEventGrpComp.decode noEvents.toNat bytes
  let (trdClearingPriceLegGrpComp_, bytes) ← decodeMany TrdClearingPriceLegGrpComp.decode noLegClearingPrices.toNat bytes
  let (instrumentAttributeGrpComp_, bytes) ← decodeMany InstrumentAttributeGrpComp.decode noInstrAttrib.toNat bytes
  let (underlyingStipGrpComp_, bytes) ← decodeMany UnderlyingStipGrpComp.decode noUnderlyingStips.toNat bytes
  let (varText_, bytes) ← decodeMany Byte.decode varTextLen.toNat bytes
  let alignmentPadding_ := bytes
  if fits_sideAllocGrpBcComp : sideAllocGrpBcComp_.length < 256 ^ 1 then
    if fits_trdInstrmntLegGrpComp : trdInstrmntLegGrpComp_.length < 256 ^ 1 then
      if fits_instrumentEventGrpComp : instrumentEventGrpComp_.length < 256 ^ 1 then
        if fits_trdClearingPriceLegGrpComp : trdClearingPriceLegGrpComp_.length < 256 ^ 1 then
          if fits_instrumentAttributeGrpComp : instrumentAttributeGrpComp_.length < 256 ^ 1 then
            if fits_underlyingStipGrpComp : underlyingStipGrpComp_.length < 256 ^ 1 then
              if fits_varText : varText_.length < 256 ^ 2 then
                if fits_alignmentPadding : alignmentPadding_.length ≤ 4282374239 then
                  pure { pad2, rbcHeaderComp, securityId, lastPx, transactTime, underlyingPx, transBkdTime, relatedClosePrice, relatedTradeQuantity, relatedSecurityId, relatedPx, underlyingQty, marketSegmentId, packageId, tesExecId, underlyingSettlementDate, underlyingMaturityDate, relatedTradeId, relatedMarketSegmentId, autoApprovalRuleId, trdType, tradeReportType, trdRptStatus, productComplex, tradePublishIndicator, partyIdSettlementLocation, hedgeType, swapClearer, messageEventSource, tradeReportText, tradeReportId, rootPartyExecutingFirm, rootPartyExecutingTrader, underlyingSecurityId, underlyingSecurityDesc, underlyingCurrency, underlyingIssuer, sideAllocGrpBcComp := ⟨sideAllocGrpBcComp_, fits_sideAllocGrpBcComp⟩, trdInstrmntLegGrpComp := ⟨trdInstrmntLegGrpComp_, fits_trdInstrmntLegGrpComp⟩, instrumentEventGrpComp := ⟨instrumentEventGrpComp_, fits_instrumentEventGrpComp⟩, trdClearingPriceLegGrpComp := ⟨trdClearingPriceLegGrpComp_, fits_trdClearingPriceLegGrpComp⟩, instrumentAttributeGrpComp := ⟨instrumentAttributeGrpComp_, fits_instrumentAttributeGrpComp⟩, underlyingStipGrpComp := ⟨underlyingStipGrpComp_, fits_underlyingStipGrpComp⟩, varText := ⟨varText_, fits_varText⟩, alignmentPadding := ⟨alignmentPadding_, fits_alignmentPadding⟩ }
                else none
              else none
            else none
          else none
        else none
      else none
    else none
  else none

theorem encode_length_pos (message : TesBroadcast) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : TesBroadcast) : (encode message).length ≤ 4282482904 := by
  have bound_sideAllocGrpBcComp := message.sideAllocGrpBcComp.length_lt
  have bound_trdInstrmntLegGrpComp := message.trdInstrmntLegGrpComp.length_lt
  have bound_instrumentEventGrpComp := message.instrumentEventGrpComp.length_lt
  have bound_trdClearingPriceLegGrpComp := message.trdClearingPriceLegGrpComp.length_lt
  have bound_instrumentAttributeGrpComp := message.instrumentAttributeGrpComp.length_lt
  have bound_underlyingStipGrpComp := message.underlyingStipGrpComp.length_lt
  have bound_varText := message.varText.length_lt
  have bound_alignmentPadding := message.alignmentPadding.length_le
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RbcHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length, MessageEventSource.encode_length, encodeMany_length_const SideAllocGrpBcComp.encode 40 SideAllocGrpBcComp.encode_length, encodeMany_length_const TrdInstrmntLegGrpComp.encode 24 TrdInstrmntLegGrpComp.encode_length, encodeMany_length_const InstrumentEventGrpComp.encode 8 InstrumentEventGrpComp.encode_length, encodeMany_length_const TrdClearingPriceLegGrpComp.encode 16 TrdClearingPriceLegGrpComp.encode_length, encodeMany_length_const InstrumentAttributeGrpComp.encode 40 InstrumentAttributeGrpComp.encode_length, encodeMany_length_const UnderlyingStipGrpComp.encode 40 UnderlyingStipGrpComp.encode_length, encodeMany_length_const Byte.encode 1 Byte.encode_length]
  omega

theorem decode_encode (message : TesBroadcast) : decode (encode message) = some message := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [RbcHeaderComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [MessageEventSource.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 SideAllocGrpBcComp.encode SideAllocGrpBcComp.decode SideAllocGrpBcComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 TrdInstrmntLegGrpComp.encode TrdInstrmntLegGrpComp.decode TrdInstrmntLegGrpComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 InstrumentEventGrpComp.encode InstrumentEventGrpComp.decode InstrumentEventGrpComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 TrdClearingPriceLegGrpComp.encode TrdClearingPriceLegGrpComp.decode TrdClearingPriceLegGrpComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 InstrumentAttributeGrpComp.encode InstrumentAttributeGrpComp.decode InstrumentAttributeGrpComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 UnderlyingStipGrpComp.encode UnderlyingStipGrpComp.decode UnderlyingStipGrpComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 2 Byte.encode Byte.decode Byte.decode_encode]
  simp only [Option.bind_some]
  simp only [message.sideAllocGrpBcComp.length_lt, message.trdInstrmntLegGrpComp.length_lt, message.instrumentEventGrpComp.length_lt, message.trdClearingPriceLegGrpComp.length_lt, message.instrumentAttributeGrpComp.length_lt, message.underlyingStipGrpComp.length_lt, message.varText.length_lt, message.alignmentPadding.length_le, ↓reduceDIte]
  rfl

end TesBroadcast

/-- Tes Delete Broadcast: 82 bytes -/
structure TesDeleteBroadcast where
  pad2 : Alpha 2
  rbcHeaderComp : RbcHeaderComp
  transactTime : BitVec 64
  marketSegmentId : BitVec 32
  packageId : BitVec 32
  tesExecId : BitVec 32
  trdType : BitVec 16
  deleteReason : BitVec 8
  tradeReportType : BitVec 8
  trdRptStatus : BitVec 8
  messageEventSource : MessageEventSource
  tradeReportId : Alpha 20
  pad2v2 : Alpha 2
  deriving DecidableEq, Repr

namespace TesDeleteBroadcast

def encode (message : TesDeleteBroadcast) : List UInt8 :=
  Alpha.encode message.pad2
    ++ RbcHeaderComp.encode message.rbcHeaderComp
    ++ encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 4 message.marketSegmentId
    ++ encodeUIntLE 4 message.packageId
    ++ encodeUIntLE 4 message.tesExecId
    ++ encodeUIntLE 2 message.trdType
    ++ encodeUInt 1 message.deleteReason
    ++ encodeUInt 1 message.tradeReportType
    ++ encodeUInt 1 message.trdRptStatus
    ++ MessageEventSource.encode message.messageEventSource
    ++ Alpha.encode message.tradeReportId
    ++ Alpha.encode message.pad2v2

def decode (bytes : List UInt8) : Option (TesDeleteBroadcast × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderComp, bytes) ← RbcHeaderComp.decode bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (packageId, bytes) ← decodeUIntLE 4 bytes
  let (tesExecId, bytes) ← decodeUIntLE 4 bytes
  let (trdType, bytes) ← decodeUIntLE 2 bytes
  let (deleteReason, bytes) ← decodeUInt 1 bytes
  let (tradeReportType, bytes) ← decodeUInt 1 bytes
  let (trdRptStatus, bytes) ← decodeUInt 1 bytes
  let (messageEventSource, bytes) ← MessageEventSource.decode bytes
  let (tradeReportId, bytes) ← Alpha.decode 20 bytes
  let (pad2v2, bytes) ← Alpha.decode 2 bytes
  pure ({ pad2, rbcHeaderComp, transactTime, marketSegmentId, packageId, tesExecId, trdType, deleteReason, tradeReportType, trdRptStatus, messageEventSource, tradeReportId, pad2v2 }, bytes)

@[simp] theorem encode_length (message : TesDeleteBroadcast) : (encode message).length = 82 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RbcHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length, MessageEventSource.encode_length]

theorem encode_length_pos (message : TesDeleteBroadcast) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TesDeleteBroadcast) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [RbcHeaderComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [MessageEventSource.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : TesDeleteBroadcast) : decode (encode message) = some (message, []) := by
  have trailing := decode_encode message []
  rw [List.append_nil] at trailing
  exact trailing

end TesDeleteBroadcast

/-- Tes Execution Broadcast: 66 bytes -/
structure TesExecutionBroadcast where
  pad2 : Alpha 2
  rbcHeaderComp : RbcHeaderComp
  transactTime : BitVec 64
  marketSegmentId : BitVec 32
  packageId : BitVec 32
  tesExecId : BitVec 32
  allocId : BitVec 32
  trdType : BitVec 16
  tradeReportType : BitVec 8
  side : BitVec 8
  trdRptStatus : BitVec 8
  messageEventSource : MessageEventSource
  pad2v2 : Alpha 2
  deriving DecidableEq, Repr

namespace TesExecutionBroadcast

def encode (message : TesExecutionBroadcast) : List UInt8 :=
  Alpha.encode message.pad2
    ++ RbcHeaderComp.encode message.rbcHeaderComp
    ++ encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 4 message.marketSegmentId
    ++ encodeUIntLE 4 message.packageId
    ++ encodeUIntLE 4 message.tesExecId
    ++ encodeUIntLE 4 message.allocId
    ++ encodeUIntLE 2 message.trdType
    ++ encodeUInt 1 message.tradeReportType
    ++ encodeUInt 1 message.side
    ++ encodeUInt 1 message.trdRptStatus
    ++ MessageEventSource.encode message.messageEventSource
    ++ Alpha.encode message.pad2v2

def decode (bytes : List UInt8) : Option (TesExecutionBroadcast × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderComp, bytes) ← RbcHeaderComp.decode bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (packageId, bytes) ← decodeUIntLE 4 bytes
  let (tesExecId, bytes) ← decodeUIntLE 4 bytes
  let (allocId, bytes) ← decodeUIntLE 4 bytes
  let (trdType, bytes) ← decodeUIntLE 2 bytes
  let (tradeReportType, bytes) ← decodeUInt 1 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (trdRptStatus, bytes) ← decodeUInt 1 bytes
  let (messageEventSource, bytes) ← MessageEventSource.decode bytes
  let (pad2v2, bytes) ← Alpha.decode 2 bytes
  pure ({ pad2, rbcHeaderComp, transactTime, marketSegmentId, packageId, tesExecId, allocId, trdType, tradeReportType, side, trdRptStatus, messageEventSource, pad2v2 }, bytes)

@[simp] theorem encode_length (message : TesExecutionBroadcast) : (encode message).length = 66 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RbcHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length, MessageEventSource.encode_length]

theorem encode_length_pos (message : TesExecutionBroadcast) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TesExecutionBroadcast) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [RbcHeaderComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [MessageEventSource.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : TesExecutionBroadcast) : decode (encode message) = some (message, []) := by
  have trailing := decode_encode message []
  rw [List.append_nil] at trailing
  exact trailing

end TesExecutionBroadcast

/-- Tes Response: 50 bytes -/
structure TesResponse where
  pad2 : Alpha 2
  responseHeaderComp : ResponseHeaderComp
  tesExecId : BitVec 32
  tradeReportId : Alpha 20
  deriving DecidableEq, Repr

namespace TesResponse

def encode (message : TesResponse) : List UInt8 :=
  Alpha.encode message.pad2
    ++ ResponseHeaderComp.encode message.responseHeaderComp
    ++ encodeUIntLE 4 message.tesExecId
    ++ Alpha.encode message.tradeReportId

def decode (bytes : List UInt8) : Option (TesResponse × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (responseHeaderComp, bytes) ← ResponseHeaderComp.decode bytes
  let (tesExecId, bytes) ← decodeUIntLE 4 bytes
  let (tradeReportId, bytes) ← Alpha.decode 20 bytes
  pure ({ pad2, responseHeaderComp, tesExecId, tradeReportId }, bytes)

@[simp] theorem encode_length (message : TesResponse) : (encode message).length = 50 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, ResponseHeaderComp.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : TesResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TesResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [ResponseHeaderComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : TesResponse) : decode (encode message) = some (message, []) := by
  have trailing := decode_encode message []
  rw [List.append_nil] at trailing
  exact trailing

end TesResponse

/-- Tes Reversal Broadcast -/
structure TesReversalBroadcast where
  pad2 : Alpha 2
  rbcHeaderComp : RbcHeaderComp
  reversalInitiationTime : BitVec 64
  marketSegmentId : BitVec 32
  packageId : BitVec 32
  tesExecId : BitVec 32
  relatedMarketSegmentId : BitVec 32
  trdType : BitVec 16
  trdRptStatus : BitVec 8
  reversalCancellationReason : BitVec 8
  tradeReportId : Alpha 20
  reversalReasonText : Alpha 132
  pad3 : Alpha 3
  sideAllocGrpBcComp : Bounded 1 SideAllocGrpBcComp
  deriving DecidableEq, Repr

namespace TesReversalBroadcast

def encode (message : TesReversalBroadcast) : List UInt8 :=
  Alpha.encode message.pad2
    ++ RbcHeaderComp.encode message.rbcHeaderComp
    ++ encodeUIntLE 8 message.reversalInitiationTime
    ++ encodeUIntLE 4 message.marketSegmentId
    ++ encodeUIntLE 4 message.packageId
    ++ encodeUIntLE 4 message.tesExecId
    ++ encodeUIntLE 4 message.relatedMarketSegmentId
    ++ encodeUIntLE 2 message.trdType
    ++ encodeUInt 1 message.trdRptStatus
    ++ encodeUInt 1 message.reversalCancellationReason
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.sideAllocGrpBcComp.val.length)
    ++ Alpha.encode message.tradeReportId
    ++ Alpha.encode message.reversalReasonText
    ++ Alpha.encode message.pad3
    ++ encodeMany SideAllocGrpBcComp.encode message.sideAllocGrpBcComp.val

def decode (bytes : List UInt8) : Option (TesReversalBroadcast × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderComp, bytes) ← RbcHeaderComp.decode bytes
  let (reversalInitiationTime, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (packageId, bytes) ← decodeUIntLE 4 bytes
  let (tesExecId, bytes) ← decodeUIntLE 4 bytes
  let (relatedMarketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (trdType, bytes) ← decodeUIntLE 2 bytes
  let (trdRptStatus, bytes) ← decodeUInt 1 bytes
  let (reversalCancellationReason, bytes) ← decodeUInt 1 bytes
  let (noSideAllocs, bytes) ← decodeUInt 1 bytes
  let (tradeReportId, bytes) ← Alpha.decode 20 bytes
  let (reversalReasonText, bytes) ← Alpha.decode 132 bytes
  let (pad3, bytes) ← Alpha.decode 3 bytes
  let (sideAllocGrpBcComp_, bytes) ← decodeMany SideAllocGrpBcComp.decode noSideAllocs.toNat bytes
  if fits_sideAllocGrpBcComp : sideAllocGrpBcComp_.length < 256 ^ 1 then
    pure ({ pad2, rbcHeaderComp, reversalInitiationTime, marketSegmentId, packageId, tesExecId, relatedMarketSegmentId, trdType, trdRptStatus, reversalCancellationReason, tradeReportId, reversalReasonText, pad3, sideAllocGrpBcComp := ⟨sideAllocGrpBcComp_, fits_sideAllocGrpBcComp⟩ }, bytes)
  else none

theorem encode_length_pos (message : TesReversalBroadcast) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : TesReversalBroadcast) : (encode message).length ≤ 10418 := by
  have bound_sideAllocGrpBcComp := message.sideAllocGrpBcComp.length_lt
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RbcHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const SideAllocGrpBcComp.encode 40 SideAllocGrpBcComp.encode_length]
  omega

@[simp] theorem decode_encode (message : TesReversalBroadcast) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [RbcHeaderComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 SideAllocGrpBcComp.encode SideAllocGrpBcComp.decode SideAllocGrpBcComp.decode_encode]
  simp only [Option.bind_some]
  simp only [message.sideAllocGrpBcComp.length_lt, ↓reduceDIte]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : TesReversalBroadcast) : decode (encode message) = some (message, []) := by
  have trailing := decode_encode message []
  rw [List.append_nil] at trailing
  exact trailing

end TesReversalBroadcast

/-- Tes Trade Broadcast: 458 bytes -/
structure TesTradeBroadcast where
  pad2 : Alpha 2
  rbcHeaderComp : RbcHeaderComp
  securityId : BitVec 64
  lastPx : BitVec 64
  lastQty : BitVec 64
  clearingTradePrice : BitVec 64
  clearingTradeQty : BitVec 64
  transactTime : BitVec 64
  relatedSecurityId : BitVec 64
  rootPartyIdClientId : BitVec 64
  executingTrader : BitVec 64
  rootPartyIdInvestmentDecisionMaker : BitVec 64
  basketTrdMatchId : BitVec 64
  origBasketTrdMatchId : BitVec 64
  sideLastPx : BitVec 64
  sideLastQty : BitVec 64
  relatedClosePrice : BitVec 64
  tesExecId : BitVec 32
  packageId : BitVec 32
  marketSegmentId : BitVec 32
  tradeId : BitVec 32
  tradeDate : BitVec 32
  sideTradeId : BitVec 32
  rootPartyIdSessionId : BitVec 32
  origTradeId : BitVec 32
  rootPartyIdExecutingUnit : BitVec 32
  rootPartyIdExecutingTrader : BitVec 32
  rootPartyIdClearingUnit : BitVec 32
  strategyLinkId : BitVec 32
  relatedSymbol : BitVec 32
  totNumTradeReports : BitVec 32
  negotiationId : BitVec 32
  srqsRelatedTradeId : BitVec 32
  basketProfileId : BitVec 32
  securitySubType : BitVec 32
  trdType : BitVec 16
  productComplex : BitVec 8
  relatedProductComplex : BitVec 8
  side : BitVec 8
  tradingCapacity : BitVec 8
  tradeReportType : BitVec 8
  transferReason : BitVec 8
  tradePublishIndicator : BitVec 8
  optionalEarlyTerminationIndicator : BitVec 8
  multiLegReportingType : BitVec 8
  positionEffect : PositionEffect
  multilegPriceModel : BitVec 8
  orderAttributeLiquidityProvision : BitVec 8
  orderAttributeRiskReduction : BitVec 8
  executingTraderQualifier : BitVec 8
  rootPartyIdInvestmentDecisionMakerQualifier : BitVec 8
  orderOrigination : BitVec 8
  reversalIndicator : BitVec 8
  tradeAggregationTransType : BitVec 8
  account : Alpha 2
  rootPartyIdPositionAccount : Alpha 32
  custOrderHandlingInst : CustOrderHandlingInst
  freeText1 : Alpha 12
  freeText2 : Alpha 12
  freeText3 : Alpha 12
  rootPartyExecutingFirm : Alpha 5
  rootPartyExecutingTrader : Alpha 6
  rootPartyClearingFirm : Alpha 5
  rootPartyClearingOrganization : Alpha 4
  rootPartyIdBeneficiary : Alpha 9
  rootPartyIdTakeUpTradingFirm : Alpha 5
  rootPartyIdOrderOriginationFirm : Alpha 7
  rootPartyIdExecutionVenue : Alpha 4
  regulatoryTradeId : Alpha 52
  basketPartyContraFirm : Alpha 5
  basketSideTradeReportId : Alpha 20
  feeIdntCode : Alpha 15
  pad4 : Alpha 4
  deriving DecidableEq, Repr

namespace TesTradeBroadcast

def encode (message : TesTradeBroadcast) : List UInt8 :=
  Alpha.encode message.pad2
    ++ RbcHeaderComp.encode message.rbcHeaderComp
    ++ encodeUIntLE 8 message.securityId
    ++ encodeUIntLE 8 message.lastPx
    ++ encodeUIntLE 8 message.lastQty
    ++ encodeUIntLE 8 message.clearingTradePrice
    ++ encodeUIntLE 8 message.clearingTradeQty
    ++ encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 8 message.relatedSecurityId
    ++ encodeUIntLE 8 message.rootPartyIdClientId
    ++ encodeUIntLE 8 message.executingTrader
    ++ encodeUIntLE 8 message.rootPartyIdInvestmentDecisionMaker
    ++ encodeUIntLE 8 message.basketTrdMatchId
    ++ encodeUIntLE 8 message.origBasketTrdMatchId
    ++ encodeUIntLE 8 message.sideLastPx
    ++ encodeUIntLE 8 message.sideLastQty
    ++ encodeUIntLE 8 message.relatedClosePrice
    ++ encodeUIntLE 4 message.tesExecId
    ++ encodeUIntLE 4 message.packageId
    ++ encodeUIntLE 4 message.marketSegmentId
    ++ encodeUIntLE 4 message.tradeId
    ++ encodeUIntLE 4 message.tradeDate
    ++ encodeUIntLE 4 message.sideTradeId
    ++ encodeUIntLE 4 message.rootPartyIdSessionId
    ++ encodeUIntLE 4 message.origTradeId
    ++ encodeUIntLE 4 message.rootPartyIdExecutingUnit
    ++ encodeUIntLE 4 message.rootPartyIdExecutingTrader
    ++ encodeUIntLE 4 message.rootPartyIdClearingUnit
    ++ encodeUIntLE 4 message.strategyLinkId
    ++ encodeUIntLE 4 message.relatedSymbol
    ++ encodeUIntLE 4 message.totNumTradeReports
    ++ encodeUIntLE 4 message.negotiationId
    ++ encodeUIntLE 4 message.srqsRelatedTradeId
    ++ encodeUIntLE 4 message.basketProfileId
    ++ encodeUIntLE 4 message.securitySubType
    ++ encodeUIntLE 2 message.trdType
    ++ encodeUInt 1 message.productComplex
    ++ encodeUInt 1 message.relatedProductComplex
    ++ encodeUInt 1 message.side
    ++ encodeUInt 1 message.tradingCapacity
    ++ encodeUInt 1 message.tradeReportType
    ++ encodeUInt 1 message.transferReason
    ++ encodeUInt 1 message.tradePublishIndicator
    ++ encodeUInt 1 message.optionalEarlyTerminationIndicator
    ++ encodeUInt 1 message.multiLegReportingType
    ++ PositionEffect.encode message.positionEffect
    ++ encodeUInt 1 message.multilegPriceModel
    ++ encodeUInt 1 message.orderAttributeLiquidityProvision
    ++ encodeUInt 1 message.orderAttributeRiskReduction
    ++ encodeUInt 1 message.executingTraderQualifier
    ++ encodeUInt 1 message.rootPartyIdInvestmentDecisionMakerQualifier
    ++ encodeUInt 1 message.orderOrigination
    ++ encodeUInt 1 message.reversalIndicator
    ++ encodeUInt 1 message.tradeAggregationTransType
    ++ Alpha.encode message.account
    ++ Alpha.encode message.rootPartyIdPositionAccount
    ++ CustOrderHandlingInst.encode message.custOrderHandlingInst
    ++ Alpha.encode message.freeText1
    ++ Alpha.encode message.freeText2
    ++ Alpha.encode message.freeText3
    ++ Alpha.encode message.rootPartyExecutingFirm
    ++ Alpha.encode message.rootPartyExecutingTrader
    ++ Alpha.encode message.rootPartyClearingFirm
    ++ Alpha.encode message.rootPartyClearingOrganization
    ++ Alpha.encode message.rootPartyIdBeneficiary
    ++ Alpha.encode message.rootPartyIdTakeUpTradingFirm
    ++ Alpha.encode message.rootPartyIdOrderOriginationFirm
    ++ Alpha.encode message.rootPartyIdExecutionVenue
    ++ Alpha.encode message.regulatoryTradeId
    ++ Alpha.encode message.basketPartyContraFirm
    ++ Alpha.encode message.basketSideTradeReportId
    ++ Alpha.encode message.feeIdntCode
    ++ Alpha.encode message.pad4

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (TesTradeBroadcast × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderComp, bytes) ← RbcHeaderComp.decode bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  let (lastQty, bytes) ← decodeUIntLE 8 bytes
  let (clearingTradePrice, bytes) ← decodeUIntLE 8 bytes
  let (clearingTradeQty, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (relatedSecurityId, bytes) ← decodeUIntLE 8 bytes
  let (rootPartyIdClientId, bytes) ← decodeUIntLE 8 bytes
  let (executingTrader, bytes) ← decodeUIntLE 8 bytes
  let (rootPartyIdInvestmentDecisionMaker, bytes) ← decodeUIntLE 8 bytes
  let (basketTrdMatchId, bytes) ← decodeUIntLE 8 bytes
  let (origBasketTrdMatchId, bytes) ← decodeUIntLE 8 bytes
  let (sideLastPx, bytes) ← decodeUIntLE 8 bytes
  let (sideLastQty, bytes) ← decodeUIntLE 8 bytes
  let (relatedClosePrice, bytes) ← decodeUIntLE 8 bytes
  let (tesExecId, bytes) ← decodeUIntLE 4 bytes
  let (packageId, bytes) ← decodeUIntLE 4 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (tradeId, bytes) ← decodeUIntLE 4 bytes
  let (tradeDate, bytes) ← decodeUIntLE 4 bytes
  let (sideTradeId, bytes) ← decodeUIntLE 4 bytes
  let (rootPartyIdSessionId, bytes) ← decodeUIntLE 4 bytes
  let (origTradeId, bytes) ← decodeUIntLE 4 bytes
  let (rootPartyIdExecutingUnit, bytes) ← decodeUIntLE 4 bytes
  let (rootPartyIdExecutingTrader, bytes) ← decodeUIntLE 4 bytes
  let (rootPartyIdClearingUnit, bytes) ← decodeUIntLE 4 bytes
  let (strategyLinkId, bytes) ← decodeUIntLE 4 bytes
  let (relatedSymbol, bytes) ← decodeUIntLE 4 bytes
  let (totNumTradeReports, bytes) ← decodeUIntLE 4 bytes
  let (negotiationId, bytes) ← decodeUIntLE 4 bytes
  let (srqsRelatedTradeId, bytes) ← decodeUIntLE 4 bytes
  let (basketProfileId, bytes) ← decodeUIntLE 4 bytes
  let (securitySubType, bytes) ← decodeUIntLE 4 bytes
  let (trdType, bytes) ← decodeUIntLE 2 bytes
  let (productComplex, bytes) ← decodeUInt 1 bytes
  let (relatedProductComplex, bytes) ← decodeUInt 1 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (tradingCapacity, bytes) ← decodeUInt 1 bytes
  let (tradeReportType, bytes) ← decodeUInt 1 bytes
  let (transferReason, bytes) ← decodeUInt 1 bytes
  let (tradePublishIndicator, bytes) ← decodeUInt 1 bytes
  let (optionalEarlyTerminationIndicator, bytes) ← decodeUInt 1 bytes
  let (multiLegReportingType, bytes) ← decodeUInt 1 bytes
  let (positionEffect, bytes) ← PositionEffect.decode bytes
  let (multilegPriceModel, bytes) ← decodeUInt 1 bytes
  let (orderAttributeLiquidityProvision, bytes) ← decodeUInt 1 bytes
  let (orderAttributeRiskReduction, bytes) ← decodeUInt 1 bytes
  let (executingTraderQualifier, bytes) ← decodeUInt 1 bytes
  let (rootPartyIdInvestmentDecisionMakerQualifier, bytes) ← decodeUInt 1 bytes
  let (orderOrigination, bytes) ← decodeUInt 1 bytes
  let (reversalIndicator, bytes) ← decodeUInt 1 bytes
  let (tradeAggregationTransType, bytes) ← decodeUInt 1 bytes
  let (account, bytes) ← Alpha.decode 2 bytes
  let (rootPartyIdPositionAccount, bytes) ← Alpha.decode 32 bytes
  let (custOrderHandlingInst, bytes) ← CustOrderHandlingInst.decode bytes
  let (freeText1, bytes) ← Alpha.decode 12 bytes
  let (freeText2, bytes) ← Alpha.decode 12 bytes
  let (freeText3, bytes) ← Alpha.decode 12 bytes
  let (rootPartyExecutingFirm, bytes) ← Alpha.decode 5 bytes
  let (rootPartyExecutingTrader, bytes) ← Alpha.decode 6 bytes
  let (rootPartyClearingFirm, bytes) ← Alpha.decode 5 bytes
  let (rootPartyClearingOrganization, bytes) ← Alpha.decode 4 bytes
  let (rootPartyIdBeneficiary, bytes) ← Alpha.decode 9 bytes
  let (rootPartyIdTakeUpTradingFirm, bytes) ← Alpha.decode 5 bytes
  let (rootPartyIdOrderOriginationFirm, bytes) ← Alpha.decode 7 bytes
  let (rootPartyIdExecutionVenue, bytes) ← Alpha.decode 4 bytes
  let (regulatoryTradeId, bytes) ← Alpha.decode 52 bytes
  let (basketPartyContraFirm, bytes) ← Alpha.decode 5 bytes
  let (basketSideTradeReportId, bytes) ← Alpha.decode 20 bytes
  let (feeIdntCode, bytes) ← Alpha.decode 15 bytes
  let (pad4, bytes) ← Alpha.decode 4 bytes
  pure ({ pad2, rbcHeaderComp, securityId, lastPx, lastQty, clearingTradePrice, clearingTradeQty, transactTime, relatedSecurityId, rootPartyIdClientId, executingTrader, rootPartyIdInvestmentDecisionMaker, basketTrdMatchId, origBasketTrdMatchId, sideLastPx, sideLastQty, relatedClosePrice, tesExecId, packageId, marketSegmentId, tradeId, tradeDate, sideTradeId, rootPartyIdSessionId, origTradeId, rootPartyIdExecutingUnit, rootPartyIdExecutingTrader, rootPartyIdClearingUnit, strategyLinkId, relatedSymbol, totNumTradeReports, negotiationId, srqsRelatedTradeId, basketProfileId, securitySubType, trdType, productComplex, relatedProductComplex, side, tradingCapacity, tradeReportType, transferReason, tradePublishIndicator, optionalEarlyTerminationIndicator, multiLegReportingType, positionEffect, multilegPriceModel, orderAttributeLiquidityProvision, orderAttributeRiskReduction, executingTraderQualifier, rootPartyIdInvestmentDecisionMakerQualifier, orderOrigination, reversalIndicator, tradeAggregationTransType, account, rootPartyIdPositionAccount, custOrderHandlingInst, freeText1, freeText2, freeText3, rootPartyExecutingFirm, rootPartyExecutingTrader, rootPartyClearingFirm, rootPartyClearingOrganization, rootPartyIdBeneficiary, rootPartyIdTakeUpTradingFirm, rootPartyIdOrderOriginationFirm, rootPartyIdExecutionVenue, regulatoryTradeId, basketPartyContraFirm, basketSideTradeReportId, feeIdntCode, pad4 }, bytes)

@[simp] theorem encode_length (message : TesTradeBroadcast) : (encode message).length = 458 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RbcHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length, PositionEffect.encode_length, CustOrderHandlingInst.encode_length]

theorem encode_length_pos (message : TesTradeBroadcast) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TesTradeBroadcast) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [RbcHeaderComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [PositionEffect.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [CustOrderHandlingInst.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : TesTradeBroadcast) : decode (encode message) = some (message, []) := by
  have trailing := decode_encode message []
  rw [List.append_nil] at trailing
  exact trailing

end TesTradeBroadcast

/-- Tes Trading Session Status Broadcast: 42 bytes -/
structure TesTradingSessionStatusBroadcast where
  pad2 : Alpha 2
  rbcHeaderComp : RbcHeaderComp
  tradeDate : BitVec 32
  tradSesEvent : BitVec 8
  pad3 : Alpha 3
  deriving DecidableEq, Repr

namespace TesTradingSessionStatusBroadcast

def encode (message : TesTradingSessionStatusBroadcast) : List UInt8 :=
  Alpha.encode message.pad2
    ++ RbcHeaderComp.encode message.rbcHeaderComp
    ++ encodeUIntLE 4 message.tradeDate
    ++ encodeUInt 1 message.tradSesEvent
    ++ Alpha.encode message.pad3

def decode (bytes : List UInt8) : Option (TesTradingSessionStatusBroadcast × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderComp, bytes) ← RbcHeaderComp.decode bytes
  let (tradeDate, bytes) ← decodeUIntLE 4 bytes
  let (tradSesEvent, bytes) ← decodeUInt 1 bytes
  let (pad3, bytes) ← Alpha.decode 3 bytes
  pure ({ pad2, rbcHeaderComp, tradeDate, tradSesEvent, pad3 }, bytes)

@[simp] theorem encode_length (message : TesTradingSessionStatusBroadcast) : (encode message).length = 42 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RbcHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : TesTradingSessionStatusBroadcast) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TesTradingSessionStatusBroadcast) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [RbcHeaderComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : TesTradingSessionStatusBroadcast) : decode (encode message) = some (message, []) := by
  have trailing := decode_encode message []
  rw [List.append_nil] at trailing
  exact trailing

end TesTradingSessionStatusBroadcast

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
    ++ encodeUIntLE 8 message.partyIdClientId
    ++ encodeUIntLE 8 message.partyIdInvestmentDecisionMaker
    ++ encodeUIntLE 8 message.executingTrader
    ++ encodeUIntLE 4 message.individualAllocId
    ++ Alpha.encode message.partyExecutingFirm
    ++ Alpha.encode message.partyExecutingTrader
    ++ Alpha.encode message.pad1
    ++ encodeUIntLE 4 message.tesEnrichmentRuleId
    ++ encodeUInt 1 message.side
    ++ encodeUInt 1 message.tradeAllocStatus
    ++ encodeUInt 1 message.tradingCapacity
    ++ PositionEffect.encode message.positionEffect
    ++ encodeUInt 1 message.orderAttributeLiquidityProvision
    ++ encodeUInt 1 message.executingTraderQualifier
    ++ encodeUInt 1 message.partyIdInvestmentDecisionMakerQualifier
    ++ encodeUInt 1 message.orderAttributeRiskReduction
    ++ encodeUInt 1 message.orderOrigination
    ++ Alpha.encode message.account
    ++ Alpha.encode message.partyIdPositionAccount
    ++ Alpha.encode message.partyIdTakeUpTradingFirm
    ++ Alpha.encode message.freeText1
    ++ Alpha.encode message.freeText2
    ++ Alpha.encode message.freeText3
    ++ Alpha.encode message.partyIdOrderOriginationFirm
    ++ Alpha.encode message.partyIdBeneficiary
    ++ Alpha.encode message.partyIdLocationId
    ++ CustOrderHandlingInst.encode message.custOrderHandlingInst
    ++ Alpha.encode message.complianceText
    ++ Alpha.encode message.partyEndClientIdentification
    ++ Alpha.encode message.pad5

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

@[simp] theorem decode_encode (message : SideAllocExtGrpComp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [PositionEffect.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [CustOrderHandlingInst.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

end SideAllocExtGrpComp

/-- Tes Upload Broadcast -/
structure TesUploadBroadcast where
  pad2 : Alpha 2
  rbcHeaderComp : RbcHeaderComp
  securityId : BitVec 64
  lastPx : BitVec 64
  transBkdTime : BitVec 64
  transactTime : BitVec 64
  underlyingPx : BitVec 64
  relatedClosePrice : BitVec 64
  relatedTradeQuantity : BitVec 64
  relatedPx : BitVec 64
  underlyingQty : BitVec 64
  marketSegmentId : BitVec 32
  packageId : BitVec 32
  tesExecId : BitVec 32
  underlyingSettlementDate : BitVec 32
  underlyingMaturityDate : BitVec 32
  relatedTradeId : BitVec 32
  relatedMarketSegmentId : BitVec 32
  trdType : BitVec 16
  productComplex : BitVec 8
  tradeReportType : BitVec 8
  trdRptStatus : BitVec 8
  tradePublishIndicator : BitVec 8
  tradePlatform : BitVec 8
  hedgeType : BitVec 8
  partyIdSettlementLocation : BitVec 8
  swapClearer : BitVec 8
  messageEventSource : MessageEventSource
  tradeReportId : Alpha 20
  rootPartyExecutingFirm : Alpha 5
  rootPartyExecutingTrader : Alpha 6
  underlyingSecurityId : Alpha 12
  underlyingSecurityDesc : Alpha 30
  underlyingCurrency : Alpha 3
  underlyingIssuer : Alpha 30
  pad2v2 : Alpha 2
  sideAllocExtGrpComp : Bounded 1 SideAllocExtGrpComp
  trdInstrmntLegGrpComp : Bounded 1 TrdInstrmntLegGrpComp
  instrumentEventGrpComp : Bounded 1 InstrumentEventGrpComp
  instrumentAttributeGrpComp : Bounded 1 InstrumentAttributeGrpComp
  underlyingStipGrpComp : Bounded 1 UnderlyingStipGrpComp
  deriving DecidableEq, Repr

namespace TesUploadBroadcast

def encode (message : TesUploadBroadcast) : List UInt8 :=
  Alpha.encode message.pad2
    ++ RbcHeaderComp.encode message.rbcHeaderComp
    ++ encodeUIntLE 8 message.securityId
    ++ encodeUIntLE 8 message.lastPx
    ++ encodeUIntLE 8 message.transBkdTime
    ++ encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 8 message.underlyingPx
    ++ encodeUIntLE 8 message.relatedClosePrice
    ++ encodeUIntLE 8 message.relatedTradeQuantity
    ++ encodeUIntLE 8 message.relatedPx
    ++ encodeUIntLE 8 message.underlyingQty
    ++ encodeUIntLE 4 message.marketSegmentId
    ++ encodeUIntLE 4 message.packageId
    ++ encodeUIntLE 4 message.tesExecId
    ++ encodeUIntLE 4 message.underlyingSettlementDate
    ++ encodeUIntLE 4 message.underlyingMaturityDate
    ++ encodeUIntLE 4 message.relatedTradeId
    ++ encodeUIntLE 4 message.relatedMarketSegmentId
    ++ encodeUIntLE 2 message.trdType
    ++ encodeUInt 1 message.productComplex
    ++ encodeUInt 1 message.tradeReportType
    ++ encodeUInt 1 message.trdRptStatus
    ++ encodeUInt 1 message.tradePublishIndicator
    ++ encodeUInt 1 message.tradePlatform
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.sideAllocExtGrpComp.val.length)
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.trdInstrmntLegGrpComp.val.length)
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.instrumentEventGrpComp.val.length)
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.instrumentAttributeGrpComp.val.length)
    ++ encodeUInt 1 (BitVec.ofNat (8 * 1) message.underlyingStipGrpComp.val.length)
    ++ encodeUInt 1 message.hedgeType
    ++ encodeUInt 1 message.partyIdSettlementLocation
    ++ encodeUInt 1 message.swapClearer
    ++ MessageEventSource.encode message.messageEventSource
    ++ Alpha.encode message.tradeReportId
    ++ Alpha.encode message.rootPartyExecutingFirm
    ++ Alpha.encode message.rootPartyExecutingTrader
    ++ Alpha.encode message.underlyingSecurityId
    ++ Alpha.encode message.underlyingSecurityDesc
    ++ Alpha.encode message.underlyingCurrency
    ++ Alpha.encode message.underlyingIssuer
    ++ Alpha.encode message.pad2v2
    ++ encodeMany SideAllocExtGrpComp.encode message.sideAllocExtGrpComp.val
    ++ encodeMany TrdInstrmntLegGrpComp.encode message.trdInstrmntLegGrpComp.val
    ++ encodeMany InstrumentEventGrpComp.encode message.instrumentEventGrpComp.val
    ++ encodeMany InstrumentAttributeGrpComp.encode message.instrumentAttributeGrpComp.val
    ++ encodeMany UnderlyingStipGrpComp.encode message.underlyingStipGrpComp.val

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (TesUploadBroadcast × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderComp, bytes) ← RbcHeaderComp.decode bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  let (transBkdTime, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (underlyingPx, bytes) ← decodeUIntLE 8 bytes
  let (relatedClosePrice, bytes) ← decodeUIntLE 8 bytes
  let (relatedTradeQuantity, bytes) ← decodeUIntLE 8 bytes
  let (relatedPx, bytes) ← decodeUIntLE 8 bytes
  let (underlyingQty, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (packageId, bytes) ← decodeUIntLE 4 bytes
  let (tesExecId, bytes) ← decodeUIntLE 4 bytes
  let (underlyingSettlementDate, bytes) ← decodeUIntLE 4 bytes
  let (underlyingMaturityDate, bytes) ← decodeUIntLE 4 bytes
  let (relatedTradeId, bytes) ← decodeUIntLE 4 bytes
  let (relatedMarketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (trdType, bytes) ← decodeUIntLE 2 bytes
  let (productComplex, bytes) ← decodeUInt 1 bytes
  let (tradeReportType, bytes) ← decodeUInt 1 bytes
  let (trdRptStatus, bytes) ← decodeUInt 1 bytes
  let (tradePublishIndicator, bytes) ← decodeUInt 1 bytes
  let (tradePlatform, bytes) ← decodeUInt 1 bytes
  let (noSideAllocs, bytes) ← decodeUInt 1 bytes
  let (noLegs, bytes) ← decodeUInt 1 bytes
  let (noEvents, bytes) ← decodeUInt 1 bytes
  let (noInstrAttrib, bytes) ← decodeUInt 1 bytes
  let (noUnderlyingStips, bytes) ← decodeUInt 1 bytes
  let (hedgeType, bytes) ← decodeUInt 1 bytes
  let (partyIdSettlementLocation, bytes) ← decodeUInt 1 bytes
  let (swapClearer, bytes) ← decodeUInt 1 bytes
  let (messageEventSource, bytes) ← MessageEventSource.decode bytes
  let (tradeReportId, bytes) ← Alpha.decode 20 bytes
  let (rootPartyExecutingFirm, bytes) ← Alpha.decode 5 bytes
  let (rootPartyExecutingTrader, bytes) ← Alpha.decode 6 bytes
  let (underlyingSecurityId, bytes) ← Alpha.decode 12 bytes
  let (underlyingSecurityDesc, bytes) ← Alpha.decode 30 bytes
  let (underlyingCurrency, bytes) ← Alpha.decode 3 bytes
  let (underlyingIssuer, bytes) ← Alpha.decode 30 bytes
  let (pad2v2, bytes) ← Alpha.decode 2 bytes
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
            pure ({ pad2, rbcHeaderComp, securityId, lastPx, transBkdTime, transactTime, underlyingPx, relatedClosePrice, relatedTradeQuantity, relatedPx, underlyingQty, marketSegmentId, packageId, tesExecId, underlyingSettlementDate, underlyingMaturityDate, relatedTradeId, relatedMarketSegmentId, trdType, productComplex, tradeReportType, trdRptStatus, tradePublishIndicator, tradePlatform, hedgeType, partyIdSettlementLocation, swapClearer, messageEventSource, tradeReportId, rootPartyExecutingFirm, rootPartyExecutingTrader, underlyingSecurityId, underlyingSecurityDesc, underlyingCurrency, underlyingIssuer, pad2v2, sideAllocExtGrpComp := ⟨sideAllocExtGrpComp_, fits_sideAllocExtGrpComp⟩, trdInstrmntLegGrpComp := ⟨trdInstrmntLegGrpComp_, fits_trdInstrmntLegGrpComp⟩, instrumentEventGrpComp := ⟨instrumentEventGrpComp_, fits_instrumentEventGrpComp⟩, instrumentAttributeGrpComp := ⟨instrumentAttributeGrpComp_, fits_instrumentAttributeGrpComp⟩, underlyingStipGrpComp := ⟨underlyingStipGrpComp_, fits_underlyingStipGrpComp⟩ }, bytes)
          else none
        else none
      else none
    else none
  else none

theorem encode_length_pos (message : TesUploadBroadcast) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : TesUploadBroadcast) : (encode message).length ≤ 79818 := by
  have bound_sideAllocExtGrpComp := message.sideAllocExtGrpComp.length_lt
  have bound_trdInstrmntLegGrpComp := message.trdInstrmntLegGrpComp.length_lt
  have bound_instrumentEventGrpComp := message.instrumentEventGrpComp.length_lt
  have bound_instrumentAttributeGrpComp := message.instrumentAttributeGrpComp.length_lt
  have bound_underlyingStipGrpComp := message.underlyingStipGrpComp.length_lt
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RbcHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length, MessageEventSource.encode_length, encodeMany_length_const SideAllocExtGrpComp.encode 200 SideAllocExtGrpComp.encode_length, encodeMany_length_const TrdInstrmntLegGrpComp.encode 24 TrdInstrmntLegGrpComp.encode_length, encodeMany_length_const InstrumentEventGrpComp.encode 8 InstrumentEventGrpComp.encode_length, encodeMany_length_const InstrumentAttributeGrpComp.encode 40 InstrumentAttributeGrpComp.encode_length, encodeMany_length_const UnderlyingStipGrpComp.encode 40 UnderlyingStipGrpComp.encode_length]
  omega

@[simp] theorem decode_encode (message : TesUploadBroadcast) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [RbcHeaderComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [MessageEventSource.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 SideAllocExtGrpComp.encode SideAllocExtGrpComp.decode SideAllocExtGrpComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 TrdInstrmntLegGrpComp.encode TrdInstrmntLegGrpComp.decode TrdInstrmntLegGrpComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 InstrumentEventGrpComp.encode InstrumentEventGrpComp.decode InstrumentEventGrpComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 InstrumentAttributeGrpComp.encode InstrumentAttributeGrpComp.decode InstrumentAttributeGrpComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 1 UnderlyingStipGrpComp.encode UnderlyingStipGrpComp.decode UnderlyingStipGrpComp.decode_encode]
  simp only [Option.bind_some]
  simp only [message.sideAllocExtGrpComp.length_lt, message.trdInstrmntLegGrpComp.length_lt, message.instrumentEventGrpComp.length_lt, message.instrumentAttributeGrpComp.length_lt, message.underlyingStipGrpComp.length_lt, ↓reduceDIte]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : TesUploadBroadcast) : decode (encode message) = some (message, []) := by
  have trailing := decode_encode message []
  rw [List.append_nil] at trailing
  exact trailing

end TesUploadBroadcast

/-- Tm Trading Session Status Broadcast: 42 bytes -/
structure TmTradingSessionStatusBroadcast where
  pad2 : Alpha 2
  rbcHeaderComp : RbcHeaderComp
  tradSesEvent : BitVec 8
  pad7 : Alpha 7
  deriving DecidableEq, Repr

namespace TmTradingSessionStatusBroadcast

def encode (message : TmTradingSessionStatusBroadcast) : List UInt8 :=
  Alpha.encode message.pad2
    ++ RbcHeaderComp.encode message.rbcHeaderComp
    ++ encodeUInt 1 message.tradSesEvent
    ++ Alpha.encode message.pad7

def decode (bytes : List UInt8) : Option (TmTradingSessionStatusBroadcast × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderComp, bytes) ← RbcHeaderComp.decode bytes
  let (tradSesEvent, bytes) ← decodeUInt 1 bytes
  let (pad7, bytes) ← Alpha.decode 7 bytes
  pure ({ pad2, rbcHeaderComp, tradSesEvent, pad7 }, bytes)

@[simp] theorem encode_length (message : TmTradingSessionStatusBroadcast) : (encode message).length = 42 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RbcHeaderComp.encode_length, encodeUInt_length]

theorem encode_length_pos (message : TmTradingSessionStatusBroadcast) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TmTradingSessionStatusBroadcast) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [RbcHeaderComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : TmTradingSessionStatusBroadcast) : decode (encode message) = some (message, []) := by
  have trailing := decode_encode message []
  rw [List.append_nil] at trailing
  exact trailing

end TmTradingSessionStatusBroadcast

/-- Throttle Update Notification: 26 bytes -/
structure ThrottleUpdateNotification where
  pad2 : Alpha 2
  notifHeaderComp : NotifHeaderComp
  throttleTimeInterval : BitVec 64
  throttleNoMsgs : BitVec 32
  throttleDisconnectLimit : BitVec 32
  deriving DecidableEq, Repr

namespace ThrottleUpdateNotification

def encode (message : ThrottleUpdateNotification) : List UInt8 :=
  Alpha.encode message.pad2
    ++ NotifHeaderComp.encode message.notifHeaderComp
    ++ encodeUIntLE 8 message.throttleTimeInterval
    ++ encodeUIntLE 4 message.throttleNoMsgs
    ++ encodeUIntLE 4 message.throttleDisconnectLimit

def decode (bytes : List UInt8) : Option (ThrottleUpdateNotification × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (notifHeaderComp, bytes) ← NotifHeaderComp.decode bytes
  let (throttleTimeInterval, bytes) ← decodeUIntLE 8 bytes
  let (throttleNoMsgs, bytes) ← decodeUIntLE 4 bytes
  let (throttleDisconnectLimit, bytes) ← decodeUIntLE 4 bytes
  pure ({ pad2, notifHeaderComp, throttleTimeInterval, throttleNoMsgs, throttleDisconnectLimit }, bytes)

@[simp] theorem encode_length (message : ThrottleUpdateNotification) : (encode message).length = 26 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, NotifHeaderComp.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : ThrottleUpdateNotification) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ThrottleUpdateNotification) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [NotifHeaderComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : ThrottleUpdateNotification) : decode (encode message) = some (message, []) := by
  have trailing := decode_encode message []
  rw [List.append_nil] at trailing
  exact trailing

end ThrottleUpdateNotification

/-- Trade Broadcast: 442 bytes -/
structure TradeBroadcast where
  pad2 : Alpha 2
  rbcHeaderComp : RbcHeaderComp
  securityId : BitVec 64
  relatedSecurityId : BitVec 64
  price : BitVec 64
  lastPx : BitVec 64
  lastQty : BitVec 64
  sideLastPx : BitVec 64
  sideLastQty : BitVec 64
  clearingTradePrice : BitVec 64
  clearingTradeQty : BitVec 64
  transactTime : BitVec 64
  orderId : BitVec 64
  clOrdId : BitVec 64
  leavesQty : BitVec 64
  cumQty : BitVec 64
  rootPartyIdClientId : BitVec 64
  executingTrader : BitVec 64
  rootPartyIdInvestmentDecisionMaker : BitVec 64
  underlyingPx : BitVec 64
  tradeId : BitVec 32
  origTradeId : BitVec 32
  massOrderReportId : BitVec 32
  rootPartyIdExecutingUnit : BitVec 32
  rootPartyIdSessionId : BitVec 32
  rootPartyIdExecutingTrader : BitVec 32
  rootPartyIdClearingUnit : BitVec 32
  marketSegmentId : BitVec 32
  relatedSymbol : BitVec 32
  sideTradeId : BitVec 32
  matchDate : BitVec 32
  trdMatchId : BitVec 32
  strategyLinkId : BitVec 32
  totNumTradeReports : BitVec 32
  securitySubType : BitVec 32
  multiLegReportingType : BitVec 8
  tradeReportType : BitVec 8
  transferReason : BitVec 8
  rootPartyIdBeneficiary : Alpha 9
  rootPartyIdTakeUpTradingFirm : Alpha 5
  rootPartyIdOrderOriginationFirm : Alpha 7
  matchType : BitVec 8
  matchSubType : BitVec 8
  side : BitVec 8
  sideLiquidityInd : BitVec 8
  tradingCapacity : BitVec 8
  orderOrigination : BitVec 8
  orderAttributeLiquidityProvision : BitVec 8
  orderAttributeRiskReduction : BitVec 8
  executingTraderQualifier : BitVec 8
  rootPartyIdInvestmentDecisionMakerQualifier : BitVec 8
  account : Alpha 2
  rootPartyIdPositionAccount : Alpha 32
  positionEffect : PositionEffect
  custOrderHandlingInst : CustOrderHandlingInst
  freeText1 : Alpha 12
  freeText2 : Alpha 12
  freeText3 : Alpha 12
  orderCategory : OrderCategory
  ordType : BitVec 8
  relatedProductComplex : BitVec 8
  orderSide : BitVec 8
  rootPartyClearingOrganization : Alpha 4
  rootPartyExecutingFirm : Alpha 5
  rootPartyExecutingTrader : Alpha 6
  rootPartyClearingFirm : Alpha 5
  regulatoryTradeId : Alpha 52
  rootPartyIdExecutionVenue : Alpha 4
  feeIdntCode : Alpha 15
  pad3 : Alpha 3
  deriving DecidableEq, Repr

namespace TradeBroadcast

def encode (message : TradeBroadcast) : List UInt8 :=
  Alpha.encode message.pad2
    ++ RbcHeaderComp.encode message.rbcHeaderComp
    ++ encodeUIntLE 8 message.securityId
    ++ encodeUIntLE 8 message.relatedSecurityId
    ++ encodeUIntLE 8 message.price
    ++ encodeUIntLE 8 message.lastPx
    ++ encodeUIntLE 8 message.lastQty
    ++ encodeUIntLE 8 message.sideLastPx
    ++ encodeUIntLE 8 message.sideLastQty
    ++ encodeUIntLE 8 message.clearingTradePrice
    ++ encodeUIntLE 8 message.clearingTradeQty
    ++ encodeUIntLE 8 message.transactTime
    ++ encodeUIntLE 8 message.orderId
    ++ encodeUIntLE 8 message.clOrdId
    ++ encodeUIntLE 8 message.leavesQty
    ++ encodeUIntLE 8 message.cumQty
    ++ encodeUIntLE 8 message.rootPartyIdClientId
    ++ encodeUIntLE 8 message.executingTrader
    ++ encodeUIntLE 8 message.rootPartyIdInvestmentDecisionMaker
    ++ encodeUIntLE 8 message.underlyingPx
    ++ encodeUIntLE 4 message.tradeId
    ++ encodeUIntLE 4 message.origTradeId
    ++ encodeUIntLE 4 message.massOrderReportId
    ++ encodeUIntLE 4 message.rootPartyIdExecutingUnit
    ++ encodeUIntLE 4 message.rootPartyIdSessionId
    ++ encodeUIntLE 4 message.rootPartyIdExecutingTrader
    ++ encodeUIntLE 4 message.rootPartyIdClearingUnit
    ++ encodeUIntLE 4 message.marketSegmentId
    ++ encodeUIntLE 4 message.relatedSymbol
    ++ encodeUIntLE 4 message.sideTradeId
    ++ encodeUIntLE 4 message.matchDate
    ++ encodeUIntLE 4 message.trdMatchId
    ++ encodeUIntLE 4 message.strategyLinkId
    ++ encodeUIntLE 4 message.totNumTradeReports
    ++ encodeUIntLE 4 message.securitySubType
    ++ encodeUInt 1 message.multiLegReportingType
    ++ encodeUInt 1 message.tradeReportType
    ++ encodeUInt 1 message.transferReason
    ++ Alpha.encode message.rootPartyIdBeneficiary
    ++ Alpha.encode message.rootPartyIdTakeUpTradingFirm
    ++ Alpha.encode message.rootPartyIdOrderOriginationFirm
    ++ encodeUInt 1 message.matchType
    ++ encodeUInt 1 message.matchSubType
    ++ encodeUInt 1 message.side
    ++ encodeUInt 1 message.sideLiquidityInd
    ++ encodeUInt 1 message.tradingCapacity
    ++ encodeUInt 1 message.orderOrigination
    ++ encodeUInt 1 message.orderAttributeLiquidityProvision
    ++ encodeUInt 1 message.orderAttributeRiskReduction
    ++ encodeUInt 1 message.executingTraderQualifier
    ++ encodeUInt 1 message.rootPartyIdInvestmentDecisionMakerQualifier
    ++ Alpha.encode message.account
    ++ Alpha.encode message.rootPartyIdPositionAccount
    ++ PositionEffect.encode message.positionEffect
    ++ CustOrderHandlingInst.encode message.custOrderHandlingInst
    ++ Alpha.encode message.freeText1
    ++ Alpha.encode message.freeText2
    ++ Alpha.encode message.freeText3
    ++ OrderCategory.encode message.orderCategory
    ++ encodeUInt 1 message.ordType
    ++ encodeUInt 1 message.relatedProductComplex
    ++ encodeUInt 1 message.orderSide
    ++ Alpha.encode message.rootPartyClearingOrganization
    ++ Alpha.encode message.rootPartyExecutingFirm
    ++ Alpha.encode message.rootPartyExecutingTrader
    ++ Alpha.encode message.rootPartyClearingFirm
    ++ Alpha.encode message.regulatoryTradeId
    ++ Alpha.encode message.rootPartyIdExecutionVenue
    ++ Alpha.encode message.feeIdntCode
    ++ Alpha.encode message.pad3

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (TradeBroadcast × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderComp, bytes) ← RbcHeaderComp.decode bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (relatedSecurityId, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  let (lastQty, bytes) ← decodeUIntLE 8 bytes
  let (sideLastPx, bytes) ← decodeUIntLE 8 bytes
  let (sideLastQty, bytes) ← decodeUIntLE 8 bytes
  let (clearingTradePrice, bytes) ← decodeUIntLE 8 bytes
  let (clearingTradeQty, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (leavesQty, bytes) ← decodeUIntLE 8 bytes
  let (cumQty, bytes) ← decodeUIntLE 8 bytes
  let (rootPartyIdClientId, bytes) ← decodeUIntLE 8 bytes
  let (executingTrader, bytes) ← decodeUIntLE 8 bytes
  let (rootPartyIdInvestmentDecisionMaker, bytes) ← decodeUIntLE 8 bytes
  let (underlyingPx, bytes) ← decodeUIntLE 8 bytes
  let (tradeId, bytes) ← decodeUIntLE 4 bytes
  let (origTradeId, bytes) ← decodeUIntLE 4 bytes
  let (massOrderReportId, bytes) ← decodeUIntLE 4 bytes
  let (rootPartyIdExecutingUnit, bytes) ← decodeUIntLE 4 bytes
  let (rootPartyIdSessionId, bytes) ← decodeUIntLE 4 bytes
  let (rootPartyIdExecutingTrader, bytes) ← decodeUIntLE 4 bytes
  let (rootPartyIdClearingUnit, bytes) ← decodeUIntLE 4 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (relatedSymbol, bytes) ← decodeUIntLE 4 bytes
  let (sideTradeId, bytes) ← decodeUIntLE 4 bytes
  let (matchDate, bytes) ← decodeUIntLE 4 bytes
  let (trdMatchId, bytes) ← decodeUIntLE 4 bytes
  let (strategyLinkId, bytes) ← decodeUIntLE 4 bytes
  let (totNumTradeReports, bytes) ← decodeUIntLE 4 bytes
  let (securitySubType, bytes) ← decodeUIntLE 4 bytes
  let (multiLegReportingType, bytes) ← decodeUInt 1 bytes
  let (tradeReportType, bytes) ← decodeUInt 1 bytes
  let (transferReason, bytes) ← decodeUInt 1 bytes
  let (rootPartyIdBeneficiary, bytes) ← Alpha.decode 9 bytes
  let (rootPartyIdTakeUpTradingFirm, bytes) ← Alpha.decode 5 bytes
  let (rootPartyIdOrderOriginationFirm, bytes) ← Alpha.decode 7 bytes
  let (matchType, bytes) ← decodeUInt 1 bytes
  let (matchSubType, bytes) ← decodeUInt 1 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (sideLiquidityInd, bytes) ← decodeUInt 1 bytes
  let (tradingCapacity, bytes) ← decodeUInt 1 bytes
  let (orderOrigination, bytes) ← decodeUInt 1 bytes
  let (orderAttributeLiquidityProvision, bytes) ← decodeUInt 1 bytes
  let (orderAttributeRiskReduction, bytes) ← decodeUInt 1 bytes
  let (executingTraderQualifier, bytes) ← decodeUInt 1 bytes
  let (rootPartyIdInvestmentDecisionMakerQualifier, bytes) ← decodeUInt 1 bytes
  let (account, bytes) ← Alpha.decode 2 bytes
  let (rootPartyIdPositionAccount, bytes) ← Alpha.decode 32 bytes
  let (positionEffect, bytes) ← PositionEffect.decode bytes
  let (custOrderHandlingInst, bytes) ← CustOrderHandlingInst.decode bytes
  let (freeText1, bytes) ← Alpha.decode 12 bytes
  let (freeText2, bytes) ← Alpha.decode 12 bytes
  let (freeText3, bytes) ← Alpha.decode 12 bytes
  let (orderCategory, bytes) ← OrderCategory.decode bytes
  let (ordType, bytes) ← decodeUInt 1 bytes
  let (relatedProductComplex, bytes) ← decodeUInt 1 bytes
  let (orderSide, bytes) ← decodeUInt 1 bytes
  let (rootPartyClearingOrganization, bytes) ← Alpha.decode 4 bytes
  let (rootPartyExecutingFirm, bytes) ← Alpha.decode 5 bytes
  let (rootPartyExecutingTrader, bytes) ← Alpha.decode 6 bytes
  let (rootPartyClearingFirm, bytes) ← Alpha.decode 5 bytes
  let (regulatoryTradeId, bytes) ← Alpha.decode 52 bytes
  let (rootPartyIdExecutionVenue, bytes) ← Alpha.decode 4 bytes
  let (feeIdntCode, bytes) ← Alpha.decode 15 bytes
  let (pad3, bytes) ← Alpha.decode 3 bytes
  pure ({ pad2, rbcHeaderComp, securityId, relatedSecurityId, price, lastPx, lastQty, sideLastPx, sideLastQty, clearingTradePrice, clearingTradeQty, transactTime, orderId, clOrdId, leavesQty, cumQty, rootPartyIdClientId, executingTrader, rootPartyIdInvestmentDecisionMaker, underlyingPx, tradeId, origTradeId, massOrderReportId, rootPartyIdExecutingUnit, rootPartyIdSessionId, rootPartyIdExecutingTrader, rootPartyIdClearingUnit, marketSegmentId, relatedSymbol, sideTradeId, matchDate, trdMatchId, strategyLinkId, totNumTradeReports, securitySubType, multiLegReportingType, tradeReportType, transferReason, rootPartyIdBeneficiary, rootPartyIdTakeUpTradingFirm, rootPartyIdOrderOriginationFirm, matchType, matchSubType, side, sideLiquidityInd, tradingCapacity, orderOrigination, orderAttributeLiquidityProvision, orderAttributeRiskReduction, executingTraderQualifier, rootPartyIdInvestmentDecisionMakerQualifier, account, rootPartyIdPositionAccount, positionEffect, custOrderHandlingInst, freeText1, freeText2, freeText3, orderCategory, ordType, relatedProductComplex, orderSide, rootPartyClearingOrganization, rootPartyExecutingFirm, rootPartyExecutingTrader, rootPartyClearingFirm, regulatoryTradeId, rootPartyIdExecutionVenue, feeIdntCode, pad3 }, bytes)

@[simp] theorem encode_length (message : TradeBroadcast) : (encode message).length = 442 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RbcHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length, PositionEffect.encode_length, CustOrderHandlingInst.encode_length, OrderCategory.encode_length]

theorem encode_length_pos (message : TradeBroadcast) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradeBroadcast) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [RbcHeaderComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [PositionEffect.decode_encode]
  simp only [Option.bind_some]
  rw [CustOrderHandlingInst.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [OrderCategory.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : TradeBroadcast) : decode (encode message) = some (message, []) := by
  have trailing := decode_encode message []
  rw [List.append_nil] at trailing
  exact trailing

end TradeBroadcast

/-- Trading Session Status Broadcast: 90 bytes -/
structure TradingSessionStatusBroadcast where
  pad2 : Alpha 2
  rbcHeaderMeComp : RbcHeaderMeComp
  marketSegmentId : BitVec 32
  tradeDate : BitVec 32
  tradSesEvent : BitVec 8
  refApplLastMsgId : Alpha 16
  pad7 : Alpha 7
  deriving DecidableEq, Repr

namespace TradingSessionStatusBroadcast

def encode (message : TradingSessionStatusBroadcast) : List UInt8 :=
  Alpha.encode message.pad2
    ++ RbcHeaderMeComp.encode message.rbcHeaderMeComp
    ++ encodeUIntLE 4 message.marketSegmentId
    ++ encodeUIntLE 4 message.tradeDate
    ++ encodeUInt 1 message.tradSesEvent
    ++ Alpha.encode message.refApplLastMsgId
    ++ Alpha.encode message.pad7

def decode (bytes : List UInt8) : Option (TradingSessionStatusBroadcast × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderMeComp, bytes) ← RbcHeaderMeComp.decode bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (tradeDate, bytes) ← decodeUIntLE 4 bytes
  let (tradSesEvent, bytes) ← decodeUInt 1 bytes
  let (refApplLastMsgId, bytes) ← Alpha.decode 16 bytes
  let (pad7, bytes) ← Alpha.decode 7 bytes
  pure ({ pad2, rbcHeaderMeComp, marketSegmentId, tradeDate, tradSesEvent, refApplLastMsgId, pad7 }, bytes)

@[simp] theorem encode_length (message : TradingSessionStatusBroadcast) : (encode message).length = 90 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RbcHeaderMeComp.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : TradingSessionStatusBroadcast) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TradingSessionStatusBroadcast) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [RbcHeaderMeComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [decodeUInt_encodeUInt]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode, Option.bind_some]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : TradingSessionStatusBroadcast) : decode (encode message) = some (message, []) := by
  have trailing := decode_encode message []
  rw [List.append_nil] at trailing
  exact trailing

end TradingSessionStatusBroadcast

/-- Unsubscribe Response: 26 bytes -/
structure UnsubscribeResponse where
  pad2 : Alpha 2
  responseHeaderComp : ResponseHeaderComp
  deriving DecidableEq, Repr

namespace UnsubscribeResponse

def encode (message : UnsubscribeResponse) : List UInt8 :=
  Alpha.encode message.pad2
    ++ ResponseHeaderComp.encode message.responseHeaderComp

def decode (bytes : List UInt8) : Option (UnsubscribeResponse × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (responseHeaderComp, bytes) ← ResponseHeaderComp.decode bytes
  pure ({ pad2, responseHeaderComp }, bytes)

@[simp] theorem encode_length (message : UnsubscribeResponse) : (encode message).length = 26 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, ResponseHeaderComp.encode_length]

theorem encode_length_pos (message : UnsubscribeResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UnsubscribeResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [ResponseHeaderComp.decode_encode, Option.bind_some]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : UnsubscribeResponse) : decode (encode message) = some (message, []) := by
  have trailing := decode_encode message []
  rw [List.append_nil] at trailing
  exact trailing

end UnsubscribeResponse

/-- Rra Update Base Party Ack Grp Comp: 8 bytes -/
structure RraUpdateBasePartyAckGrpComp where
  partyDetailExecutingUnit : Alpha 5
  pad1 : Alpha 1
  riskLimitResult : BitVec 16
  deriving DecidableEq, Repr

namespace RraUpdateBasePartyAckGrpComp

def encode (message : RraUpdateBasePartyAckGrpComp) : List UInt8 :=
  Alpha.encode message.partyDetailExecutingUnit
    ++ Alpha.encode message.pad1
    ++ encodeUIntLE 2 message.riskLimitResult

def decode (bytes : List UInt8) : Option (RraUpdateBasePartyAckGrpComp × List UInt8) := do
  let (partyDetailExecutingUnit, bytes) ← Alpha.decode 5 bytes
  let (pad1, bytes) ← Alpha.decode 1 bytes
  let (riskLimitResult, bytes) ← decodeUIntLE 2 bytes
  pure ({ partyDetailExecutingUnit, pad1, riskLimitResult }, bytes)

@[simp] theorem encode_length (message : RraUpdateBasePartyAckGrpComp) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : RraUpdateBasePartyAckGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RraUpdateBasePartyAckGrpComp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE, Option.bind_some]
  rfl

end RraUpdateBasePartyAckGrpComp

/-- Update Remaining Risk Allowance Base Response -/
structure UpdateRemainingRiskAllowanceBaseResponse where
  pad2 : Alpha 2
  nrResponseHeaderMeComp : NrResponseHeaderMeComp
  pad6 : Alpha 6
  rraUpdateBasePartyAckGrpComp : Bounded 2 RraUpdateBasePartyAckGrpComp
  deriving DecidableEq, Repr

namespace UpdateRemainingRiskAllowanceBaseResponse

def encode (message : UpdateRemainingRiskAllowanceBaseResponse) : List UInt8 :=
  Alpha.encode message.pad2
    ++ NrResponseHeaderMeComp.encode message.nrResponseHeaderMeComp
    ++ encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.rraUpdateBasePartyAckGrpComp.val.length)
    ++ Alpha.encode message.pad6
    ++ encodeMany RraUpdateBasePartyAckGrpComp.encode message.rraUpdateBasePartyAckGrpComp.val

def decode (bytes : List UInt8) : Option (UpdateRemainingRiskAllowanceBaseResponse × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (nrResponseHeaderMeComp, bytes) ← NrResponseHeaderMeComp.decode bytes
  let (noPartyRiskLimits, bytes) ← decodeUIntLE 2 bytes
  let (pad6, bytes) ← Alpha.decode 6 bytes
  let (rraUpdateBasePartyAckGrpComp_, bytes) ← decodeMany RraUpdateBasePartyAckGrpComp.decode noPartyRiskLimits.toNat bytes
  if fits_rraUpdateBasePartyAckGrpComp : rraUpdateBasePartyAckGrpComp_.length < 256 ^ 2 then
    pure ({ pad2, nrResponseHeaderMeComp, pad6, rraUpdateBasePartyAckGrpComp := ⟨rraUpdateBasePartyAckGrpComp_, fits_rraUpdateBasePartyAckGrpComp⟩ }, bytes)
  else none

theorem encode_length_pos (message : UpdateRemainingRiskAllowanceBaseResponse) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : UpdateRemainingRiskAllowanceBaseResponse) : (encode message).length ≤ 524338 := by
  have bound_rraUpdateBasePartyAckGrpComp := message.rraUpdateBasePartyAckGrpComp.length_lt
  unfold encode
  simp only [List.length_append, Alpha.encode_length, NrResponseHeaderMeComp.encode_length, encodeUIntLE_length, encodeMany_length_const RraUpdateBasePartyAckGrpComp.encode 8 RraUpdateBasePartyAckGrpComp.encode_length]
  omega

@[simp] theorem decode_encode (message : UpdateRemainingRiskAllowanceBaseResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [NrResponseHeaderMeComp.decode_encode]
  simp only [Option.bind_some]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [decodeMany_bounded 2 RraUpdateBasePartyAckGrpComp.encode RraUpdateBasePartyAckGrpComp.decode RraUpdateBasePartyAckGrpComp.decode_encode]
  simp only [Option.bind_some]
  simp only [message.rraUpdateBasePartyAckGrpComp.length_lt, ↓reduceDIte]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : UpdateRemainingRiskAllowanceBaseResponse) : decode (encode message) = some (message, []) := by
  have trailing := decode_encode message []
  rw [List.append_nil] at trailing
  exact trailing

end UpdateRemainingRiskAllowanceBaseResponse

/-- User Login Response: 26 bytes -/
structure UserLoginResponse where
  pad2 : Alpha 2
  responseHeaderComp : ResponseHeaderComp
  deriving DecidableEq, Repr

namespace UserLoginResponse

def encode (message : UserLoginResponse) : List UInt8 :=
  Alpha.encode message.pad2
    ++ ResponseHeaderComp.encode message.responseHeaderComp

def decode (bytes : List UInt8) : Option (UserLoginResponse × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (responseHeaderComp, bytes) ← ResponseHeaderComp.decode bytes
  pure ({ pad2, responseHeaderComp }, bytes)

@[simp] theorem encode_length (message : UserLoginResponse) : (encode message).length = 26 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, ResponseHeaderComp.encode_length]

theorem encode_length_pos (message : UserLoginResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UserLoginResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [ResponseHeaderComp.decode_encode, Option.bind_some]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : UserLoginResponse) : decode (encode message) = some (message, []) := by
  have trailing := decode_encode message []
  rw [List.append_nil] at trailing
  exact trailing

end UserLoginResponse

/-- User Logout Response: 26 bytes -/
structure UserLogoutResponse where
  pad2 : Alpha 2
  responseHeaderComp : ResponseHeaderComp
  deriving DecidableEq, Repr

namespace UserLogoutResponse

def encode (message : UserLogoutResponse) : List UInt8 :=
  Alpha.encode message.pad2
    ++ ResponseHeaderComp.encode message.responseHeaderComp

def decode (bytes : List UInt8) : Option (UserLogoutResponse × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (responseHeaderComp, bytes) ← ResponseHeaderComp.decode bytes
  pure ({ pad2, responseHeaderComp }, bytes)

@[simp] theorem encode_length (message : UserLogoutResponse) : (encode message).length = 26 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, ResponseHeaderComp.encode_length]

theorem encode_length_pos (message : UserLogoutResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : UserLogoutResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  simp only [List.append_assoc, Option.bind_eq_bind]
  rw [Alpha.decode_encode]
  simp only [Option.bind_some]
  rw [ResponseHeaderComp.decode_encode, Option.bind_some]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : UserLogoutResponse) : decode (encode message) = some (message, []) := by
  have trailing := decode_encode message []
  rw [List.append_nil] at trailing
  exact trailing

end UserLogoutResponse

/-- Any Server Payload, selected by Template Id -/
inductive ServerPayload where
  | addComplexInstrumentResponse (message : AddComplexInstrumentResponse) -- 10302
  | addFlexibleInstrumentResponse (message : AddFlexibleInstrumentResponse) -- 10310
  | addScaledSimpleInstrumentResponse (message : AddScaledSimpleInstrumentResponse) -- 10328
  | basketApproveBroadcast (message : BasketApproveBroadcast) -- 10627
  | basketBroadcast (message : BasketBroadcast) -- 10625
  | basketDeleteBroadcast (message : BasketDeleteBroadcast) -- 10626
  | basketExecutionBroadcast (message : BasketExecutionBroadcast) -- 10628
  | basketResponse (message : BasketResponse) -- 10624
  | basketRollBroadcast (message : BasketRollBroadcast) -- 10634
  | broadcastErrorNotification (message : BroadcastErrorNotification) -- 10032
  | clipDeletionNotification (message : ClipDeletionNotification) -- 10134
  | clipExecutionNotification (message : ClipExecutionNotification) -- 10135
  | clipResponse (message : ClipResponse) -- 10133
  | crossRequestResponse (message : CrossRequestResponse) -- 10119
  | deleteAllOrderBroadcast (message : DeleteAllOrderBroadcast) -- 10122
  | deleteAllOrderNrResponse (message : DeleteAllOrderNrResponse) -- 10124
  | deleteAllOrderQuoteEventBroadcast (message : DeleteAllOrderQuoteEventBroadcast) -- 10308
  | deleteAllOrderResponse (message : DeleteAllOrderResponse) -- 10121
  | deleteAllQuoteBroadcast (message : DeleteAllQuoteBroadcast) -- 10410
  | deleteAllQuoteResponse (message : DeleteAllQuoteResponse) -- 10409
  | deleteOrderBroadcast (message : DeleteOrderBroadcast) -- 10112
  | deleteOrderNrResponse (message : DeleteOrderNrResponse) -- 10111
  | deleteOrderResponse (message : DeleteOrderResponse) -- 10110
  | forcedLogoutNotification (message : ForcedLogoutNotification) -- 10012
  | forcedUserLogoutNotification (message : ForcedUserLogoutNotification) -- 10043
  | heartbeatNotification (message : HeartbeatNotification) -- 10023
  | inquireEnrichmentRuleIdListResponse (message : InquireEnrichmentRuleIdListResponse) -- 10041
  | inquireMmParameterResponse (message : InquireMmParameterResponse) -- 10306
  | inquireMarginBasedRiskLimitResponse (message : InquireMarginBasedRiskLimitResponse) -- 10324
  | inquireSessionListResponse (message : InquireSessionListResponse) -- 10036
  | inquireUserResponse (message : InquireUserResponse) -- 10039
  | legalNotificationBroadcast (message : LegalNotificationBroadcast) -- 10037
  | logonResponse (message : LogonResponse) -- 10001
  | logoutResponse (message : LogoutResponse) -- 10003
  | mmParameterDefinitionResponse (message : MmParameterDefinitionResponse) -- 10304
  | massOrderAck (message : MassOrderAck) -- 10116
  | massQuoteResponse (message : MassQuoteResponse) -- 10406
  | modifyOrderNrResponse (message : ModifyOrderNrResponse) -- 10108
  | modifyOrderResponse (message : ModifyOrderResponse) -- 10107
  | newOrderNrResponse (message : NewOrderNrResponse) -- 10102
  | newOrderResponse (message : NewOrderResponse) -- 10101
  | newsBroadcast (message : NewsBroadcast) -- 10031
  | orderExecNotification (message : OrderExecNotification) -- 10104
  | orderExecReportBroadcast (message : OrderExecReportBroadcast) -- 10117
  | orderExecResponse (message : OrderExecResponse) -- 10103
  | partyActionReport (message : PartyActionReport) -- 10042
  | partyEntitlementsUpdateReport (message : PartyEntitlementsUpdateReport) -- 10034
  | pingResponse (message : PingResponse) -- 10321
  | preTradeRiskLimitResponse (message : PreTradeRiskLimitResponse) -- 10313
  | quoteActivationNotification (message : QuoteActivationNotification) -- 10411
  | quoteActivationResponse (message : QuoteActivationResponse) -- 10404
  | quoteExecutionReport (message : QuoteExecutionReport) -- 10407
  | rfqResponse (message : RfqResponse) -- 10402
  | reject (message : Reject) -- 10010
  | retransmitMeMessageResponse (message : RetransmitMeMessageResponse) -- 10027
  | retransmitResponse (message : RetransmitResponse) -- 10009
  | riskNotificationBroadcast (message : RiskNotificationBroadcast) -- 10033
  | srqsCreateDealNotification (message : SrqsCreateDealNotification) -- 10708
  | srqsDealNotification (message : SrqsDealNotification) -- 10709
  | srqsDealResponse (message : SrqsDealResponse) -- 10705
  | srqsInquireSmartRespondentResponse (message : SrqsInquireSmartRespondentResponse) -- 10719
  | srqsNegotiationNotification (message : SrqsNegotiationNotification) -- 10713
  | srqsNegotiationRequesterNotification (message : SrqsNegotiationRequesterNotification) -- 10712
  | srqsNegotiationStatusNotification (message : SrqsNegotiationStatusNotification) -- 10715
  | srqsOpenNegotiationNotification (message : SrqsOpenNegotiationNotification) -- 10711
  | srqsOpenNegotiationRequesterNotification (message : SrqsOpenNegotiationRequesterNotification) -- 10710
  | srqsQuoteNotification (message : SrqsQuoteNotification) -- 10707
  | srqsQuoteResponse (message : SrqsQuoteResponse) -- 10703
  | srqsQuoteSnapshotNotification (message : SrqsQuoteSnapshotNotification) -- 10723
  | srqsResponse (message : SrqsResponse) -- 10722
  | srqsStatusBroadcast (message : SrqsStatusBroadcast) -- 10714
  | serviceAvailabilityBroadcast (message : ServiceAvailabilityBroadcast) -- 10030
  | serviceAvailabilityMarketBroadcast (message : ServiceAvailabilityMarketBroadcast) -- 10044
  | statusBroadcast (message : StatusBroadcast) -- 10045
  | subscribeResponse (message : SubscribeResponse) -- 10005
  | tesApproveBroadcast (message : TesApproveBroadcast) -- 10607
  | tesBroadcast (message : TesBroadcast) -- 10604
  | tesDeleteBroadcast (message : TesDeleteBroadcast) -- 10606
  | tesExecutionBroadcast (message : TesExecutionBroadcast) -- 10610
  | tesResponse (message : TesResponse) -- 10611
  | tesReversalBroadcast (message : TesReversalBroadcast) -- 10632
  | tesTradeBroadcast (message : TesTradeBroadcast) -- 10614
  | tesTradingSessionStatusBroadcast (message : TesTradingSessionStatusBroadcast) -- 10615
  | tesUploadBroadcast (message : TesUploadBroadcast) -- 10613
  | tmTradingSessionStatusBroadcast (message : TmTradingSessionStatusBroadcast) -- 10501
  | throttleUpdateNotification (message : ThrottleUpdateNotification) -- 10028
  | tradeBroadcast (message : TradeBroadcast) -- 10500
  | tradingSessionStatusBroadcast (message : TradingSessionStatusBroadcast) -- 10307
  | unsubscribeResponse (message : UnsubscribeResponse) -- 10007
  | updateRemainingRiskAllowanceBaseResponse (message : UpdateRemainingRiskAllowanceBaseResponse) -- 10326
  | userLoginResponse (message : UserLoginResponse) -- 10019
  | userLogoutResponse (message : UserLogoutResponse) -- 10024
  deriving DecidableEq, Repr

namespace ServerPayload

/-- The Template Id each message is sent under -/
def tag : ServerPayload → BitVec 16
  | .addComplexInstrumentResponse _ => 10302
  | .addFlexibleInstrumentResponse _ => 10310
  | .addScaledSimpleInstrumentResponse _ => 10328
  | .basketApproveBroadcast _ => 10627
  | .basketBroadcast _ => 10625
  | .basketDeleteBroadcast _ => 10626
  | .basketExecutionBroadcast _ => 10628
  | .basketResponse _ => 10624
  | .basketRollBroadcast _ => 10634
  | .broadcastErrorNotification _ => 10032
  | .clipDeletionNotification _ => 10134
  | .clipExecutionNotification _ => 10135
  | .clipResponse _ => 10133
  | .crossRequestResponse _ => 10119
  | .deleteAllOrderBroadcast _ => 10122
  | .deleteAllOrderNrResponse _ => 10124
  | .deleteAllOrderQuoteEventBroadcast _ => 10308
  | .deleteAllOrderResponse _ => 10121
  | .deleteAllQuoteBroadcast _ => 10410
  | .deleteAllQuoteResponse _ => 10409
  | .deleteOrderBroadcast _ => 10112
  | .deleteOrderNrResponse _ => 10111
  | .deleteOrderResponse _ => 10110
  | .forcedLogoutNotification _ => 10012
  | .forcedUserLogoutNotification _ => 10043
  | .heartbeatNotification _ => 10023
  | .inquireEnrichmentRuleIdListResponse _ => 10041
  | .inquireMmParameterResponse _ => 10306
  | .inquireMarginBasedRiskLimitResponse _ => 10324
  | .inquireSessionListResponse _ => 10036
  | .inquireUserResponse _ => 10039
  | .legalNotificationBroadcast _ => 10037
  | .logonResponse _ => 10001
  | .logoutResponse _ => 10003
  | .mmParameterDefinitionResponse _ => 10304
  | .massOrderAck _ => 10116
  | .massQuoteResponse _ => 10406
  | .modifyOrderNrResponse _ => 10108
  | .modifyOrderResponse _ => 10107
  | .newOrderNrResponse _ => 10102
  | .newOrderResponse _ => 10101
  | .newsBroadcast _ => 10031
  | .orderExecNotification _ => 10104
  | .orderExecReportBroadcast _ => 10117
  | .orderExecResponse _ => 10103
  | .partyActionReport _ => 10042
  | .partyEntitlementsUpdateReport _ => 10034
  | .pingResponse _ => 10321
  | .preTradeRiskLimitResponse _ => 10313
  | .quoteActivationNotification _ => 10411
  | .quoteActivationResponse _ => 10404
  | .quoteExecutionReport _ => 10407
  | .rfqResponse _ => 10402
  | .reject _ => 10010
  | .retransmitMeMessageResponse _ => 10027
  | .retransmitResponse _ => 10009
  | .riskNotificationBroadcast _ => 10033
  | .srqsCreateDealNotification _ => 10708
  | .srqsDealNotification _ => 10709
  | .srqsDealResponse _ => 10705
  | .srqsInquireSmartRespondentResponse _ => 10719
  | .srqsNegotiationNotification _ => 10713
  | .srqsNegotiationRequesterNotification _ => 10712
  | .srqsNegotiationStatusNotification _ => 10715
  | .srqsOpenNegotiationNotification _ => 10711
  | .srqsOpenNegotiationRequesterNotification _ => 10710
  | .srqsQuoteNotification _ => 10707
  | .srqsQuoteResponse _ => 10703
  | .srqsQuoteSnapshotNotification _ => 10723
  | .srqsResponse _ => 10722
  | .srqsStatusBroadcast _ => 10714
  | .serviceAvailabilityBroadcast _ => 10030
  | .serviceAvailabilityMarketBroadcast _ => 10044
  | .statusBroadcast _ => 10045
  | .subscribeResponse _ => 10005
  | .tesApproveBroadcast _ => 10607
  | .tesBroadcast _ => 10604
  | .tesDeleteBroadcast _ => 10606
  | .tesExecutionBroadcast _ => 10610
  | .tesResponse _ => 10611
  | .tesReversalBroadcast _ => 10632
  | .tesTradeBroadcast _ => 10614
  | .tesTradingSessionStatusBroadcast _ => 10615
  | .tesUploadBroadcast _ => 10613
  | .tmTradingSessionStatusBroadcast _ => 10501
  | .throttleUpdateNotification _ => 10028
  | .tradeBroadcast _ => 10500
  | .tradingSessionStatusBroadcast _ => 10307
  | .unsubscribeResponse _ => 10007
  | .updateRemainingRiskAllowanceBaseResponse _ => 10326
  | .userLoginResponse _ => 10019
  | .userLogoutResponse _ => 10024

def encode : ServerPayload → List UInt8
  | .addComplexInstrumentResponse message => AddComplexInstrumentResponse.encode message
  | .addFlexibleInstrumentResponse message => AddFlexibleInstrumentResponse.encode message
  | .addScaledSimpleInstrumentResponse message => AddScaledSimpleInstrumentResponse.encode message
  | .basketApproveBroadcast message => BasketApproveBroadcast.encode message
  | .basketBroadcast message => BasketBroadcast.encode message
  | .basketDeleteBroadcast message => BasketDeleteBroadcast.encode message
  | .basketExecutionBroadcast message => BasketExecutionBroadcast.encode message
  | .basketResponse message => BasketResponse.encode message
  | .basketRollBroadcast message => BasketRollBroadcast.encode message
  | .broadcastErrorNotification message => BroadcastErrorNotification.encode message
  | .clipDeletionNotification message => ClipDeletionNotification.encode message
  | .clipExecutionNotification message => ClipExecutionNotification.encode message
  | .clipResponse message => ClipResponse.encode message
  | .crossRequestResponse message => CrossRequestResponse.encode message
  | .deleteAllOrderBroadcast message => DeleteAllOrderBroadcast.encode message
  | .deleteAllOrderNrResponse message => DeleteAllOrderNrResponse.encode message
  | .deleteAllOrderQuoteEventBroadcast message => DeleteAllOrderQuoteEventBroadcast.encode message
  | .deleteAllOrderResponse message => DeleteAllOrderResponse.encode message
  | .deleteAllQuoteBroadcast message => DeleteAllQuoteBroadcast.encode message
  | .deleteAllQuoteResponse message => DeleteAllQuoteResponse.encode message
  | .deleteOrderBroadcast message => DeleteOrderBroadcast.encode message
  | .deleteOrderNrResponse message => DeleteOrderNrResponse.encode message
  | .deleteOrderResponse message => DeleteOrderResponse.encode message
  | .forcedLogoutNotification message => ForcedLogoutNotification.encode message
  | .forcedUserLogoutNotification message => ForcedUserLogoutNotification.encode message
  | .heartbeatNotification message => HeartbeatNotification.encode message
  | .inquireEnrichmentRuleIdListResponse message => InquireEnrichmentRuleIdListResponse.encode message
  | .inquireMmParameterResponse message => InquireMmParameterResponse.encode message
  | .inquireMarginBasedRiskLimitResponse message => InquireMarginBasedRiskLimitResponse.encode message
  | .inquireSessionListResponse message => InquireSessionListResponse.encode message
  | .inquireUserResponse message => InquireUserResponse.encode message
  | .legalNotificationBroadcast message => LegalNotificationBroadcast.encode message
  | .logonResponse message => LogonResponse.encode message
  | .logoutResponse message => LogoutResponse.encode message
  | .mmParameterDefinitionResponse message => MmParameterDefinitionResponse.encode message
  | .massOrderAck message => MassOrderAck.encode message
  | .massQuoteResponse message => MassQuoteResponse.encode message
  | .modifyOrderNrResponse message => ModifyOrderNrResponse.encode message
  | .modifyOrderResponse message => ModifyOrderResponse.encode message
  | .newOrderNrResponse message => NewOrderNrResponse.encode message
  | .newOrderResponse message => NewOrderResponse.encode message
  | .newsBroadcast message => NewsBroadcast.encode message
  | .orderExecNotification message => OrderExecNotification.encode message
  | .orderExecReportBroadcast message => OrderExecReportBroadcast.encode message
  | .orderExecResponse message => OrderExecResponse.encode message
  | .partyActionReport message => PartyActionReport.encode message
  | .partyEntitlementsUpdateReport message => PartyEntitlementsUpdateReport.encode message
  | .pingResponse message => PingResponse.encode message
  | .preTradeRiskLimitResponse message => PreTradeRiskLimitResponse.encode message
  | .quoteActivationNotification message => QuoteActivationNotification.encode message
  | .quoteActivationResponse message => QuoteActivationResponse.encode message
  | .quoteExecutionReport message => QuoteExecutionReport.encode message
  | .rfqResponse message => RfqResponse.encode message
  | .reject message => Reject.encode message
  | .retransmitMeMessageResponse message => RetransmitMeMessageResponse.encode message
  | .retransmitResponse message => RetransmitResponse.encode message
  | .riskNotificationBroadcast message => RiskNotificationBroadcast.encode message
  | .srqsCreateDealNotification message => SrqsCreateDealNotification.encode message
  | .srqsDealNotification message => SrqsDealNotification.encode message
  | .srqsDealResponse message => SrqsDealResponse.encode message
  | .srqsInquireSmartRespondentResponse message => SrqsInquireSmartRespondentResponse.encode message
  | .srqsNegotiationNotification message => SrqsNegotiationNotification.encode message
  | .srqsNegotiationRequesterNotification message => SrqsNegotiationRequesterNotification.encode message
  | .srqsNegotiationStatusNotification message => SrqsNegotiationStatusNotification.encode message
  | .srqsOpenNegotiationNotification message => SrqsOpenNegotiationNotification.encode message
  | .srqsOpenNegotiationRequesterNotification message => SrqsOpenNegotiationRequesterNotification.encode message
  | .srqsQuoteNotification message => SrqsQuoteNotification.encode message
  | .srqsQuoteResponse message => SrqsQuoteResponse.encode message
  | .srqsQuoteSnapshotNotification message => SrqsQuoteSnapshotNotification.encode message
  | .srqsResponse message => SrqsResponse.encode message
  | .srqsStatusBroadcast message => SrqsStatusBroadcast.encode message
  | .serviceAvailabilityBroadcast message => ServiceAvailabilityBroadcast.encode message
  | .serviceAvailabilityMarketBroadcast message => ServiceAvailabilityMarketBroadcast.encode message
  | .statusBroadcast message => StatusBroadcast.encode message
  | .subscribeResponse message => SubscribeResponse.encode message
  | .tesApproveBroadcast message => TesApproveBroadcast.encode message
  | .tesBroadcast message => TesBroadcast.encode message
  | .tesDeleteBroadcast message => TesDeleteBroadcast.encode message
  | .tesExecutionBroadcast message => TesExecutionBroadcast.encode message
  | .tesResponse message => TesResponse.encode message
  | .tesReversalBroadcast message => TesReversalBroadcast.encode message
  | .tesTradeBroadcast message => TesTradeBroadcast.encode message
  | .tesTradingSessionStatusBroadcast message => TesTradingSessionStatusBroadcast.encode message
  | .tesUploadBroadcast message => TesUploadBroadcast.encode message
  | .tmTradingSessionStatusBroadcast message => TmTradingSessionStatusBroadcast.encode message
  | .throttleUpdateNotification message => ThrottleUpdateNotification.encode message
  | .tradeBroadcast message => TradeBroadcast.encode message
  | .tradingSessionStatusBroadcast message => TradingSessionStatusBroadcast.encode message
  | .unsubscribeResponse message => UnsubscribeResponse.encode message
  | .updateRemainingRiskAllowanceBaseResponse message => UpdateRemainingRiskAllowanceBaseResponse.encode message
  | .userLoginResponse message => UserLoginResponse.encode message
  | .userLogoutResponse message => UserLogoutResponse.encode message

/-- Decoded from the whole of the frame: a message that reads to its end takes it all, any other must leave nothing -/
def decode (tag : BitVec 16) (bytes : List UInt8) : Option ServerPayload :=
  if tag = 10302 then (AddComplexInstrumentResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.addComplexInstrumentResponse message) else none
  else if tag = 10310 then (AddFlexibleInstrumentResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.addFlexibleInstrumentResponse message) else none
  else if tag = 10328 then (AddScaledSimpleInstrumentResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.addScaledSimpleInstrumentResponse message) else none
  else if tag = 10627 then (BasketApproveBroadcast.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.basketApproveBroadcast message) else none
  else if tag = 10625 then (BasketBroadcast.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.basketBroadcast message) else none
  else if tag = 10626 then (BasketDeleteBroadcast.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.basketDeleteBroadcast message) else none
  else if tag = 10628 then (BasketExecutionBroadcast.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.basketExecutionBroadcast message) else none
  else if tag = 10624 then (BasketResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.basketResponse message) else none
  else if tag = 10634 then (BasketRollBroadcast.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.basketRollBroadcast message) else none
  else if tag = 10032 then (BroadcastErrorNotification.decode bytes).map fun message => .broadcastErrorNotification message
  else if tag = 10134 then (ClipDeletionNotification.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.clipDeletionNotification message) else none
  else if tag = 10135 then (ClipExecutionNotification.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.clipExecutionNotification message) else none
  else if tag = 10133 then (ClipResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.clipResponse message) else none
  else if tag = 10119 then (CrossRequestResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.crossRequestResponse message) else none
  else if tag = 10122 then (DeleteAllOrderBroadcast.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.deleteAllOrderBroadcast message) else none
  else if tag = 10124 then (DeleteAllOrderNrResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.deleteAllOrderNrResponse message) else none
  else if tag = 10308 then (DeleteAllOrderQuoteEventBroadcast.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.deleteAllOrderQuoteEventBroadcast message) else none
  else if tag = 10121 then (DeleteAllOrderResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.deleteAllOrderResponse message) else none
  else if tag = 10410 then (DeleteAllQuoteBroadcast.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.deleteAllQuoteBroadcast message) else none
  else if tag = 10409 then (DeleteAllQuoteResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.deleteAllQuoteResponse message) else none
  else if tag = 10112 then (DeleteOrderBroadcast.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.deleteOrderBroadcast message) else none
  else if tag = 10111 then (DeleteOrderNrResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.deleteOrderNrResponse message) else none
  else if tag = 10110 then (DeleteOrderResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.deleteOrderResponse message) else none
  else if tag = 10012 then (ForcedLogoutNotification.decode bytes).map fun message => .forcedLogoutNotification message
  else if tag = 10043 then (ForcedUserLogoutNotification.decode bytes).map fun message => .forcedUserLogoutNotification message
  else if tag = 10023 then (HeartbeatNotification.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.heartbeatNotification message) else none
  else if tag = 10041 then (InquireEnrichmentRuleIdListResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.inquireEnrichmentRuleIdListResponse message) else none
  else if tag = 10306 then (InquireMmParameterResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.inquireMmParameterResponse message) else none
  else if tag = 10324 then (InquireMarginBasedRiskLimitResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.inquireMarginBasedRiskLimitResponse message) else none
  else if tag = 10036 then (InquireSessionListResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.inquireSessionListResponse message) else none
  else if tag = 10039 then (InquireUserResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.inquireUserResponse message) else none
  else if tag = 10037 then (LegalNotificationBroadcast.decode bytes).map fun message => .legalNotificationBroadcast message
  else if tag = 10001 then (LogonResponse.decode bytes).map fun message => .logonResponse message
  else if tag = 10003 then (LogoutResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.logoutResponse message) else none
  else if tag = 10304 then (MmParameterDefinitionResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.mmParameterDefinitionResponse message) else none
  else if tag = 10116 then (MassOrderAck.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.massOrderAck message) else none
  else if tag = 10406 then (MassQuoteResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.massQuoteResponse message) else none
  else if tag = 10108 then (ModifyOrderNrResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.modifyOrderNrResponse message) else none
  else if tag = 10107 then (ModifyOrderResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.modifyOrderResponse message) else none
  else if tag = 10102 then (NewOrderNrResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.newOrderNrResponse message) else none
  else if tag = 10101 then (NewOrderResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.newOrderResponse message) else none
  else if tag = 10031 then (NewsBroadcast.decode bytes).map fun message => .newsBroadcast message
  else if tag = 10104 then (OrderExecNotification.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.orderExecNotification message) else none
  else if tag = 10117 then (OrderExecReportBroadcast.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.orderExecReportBroadcast message) else none
  else if tag = 10103 then (OrderExecResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.orderExecResponse message) else none
  else if tag = 10042 then (PartyActionReport.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.partyActionReport message) else none
  else if tag = 10034 then (PartyEntitlementsUpdateReport.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.partyEntitlementsUpdateReport message) else none
  else if tag = 10321 then (PingResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.pingResponse message) else none
  else if tag = 10313 then (PreTradeRiskLimitResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.preTradeRiskLimitResponse message) else none
  else if tag = 10411 then (QuoteActivationNotification.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.quoteActivationNotification message) else none
  else if tag = 10404 then (QuoteActivationResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.quoteActivationResponse message) else none
  else if tag = 10407 then (QuoteExecutionReport.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.quoteExecutionReport message) else none
  else if tag = 10402 then (RfqResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.rfqResponse message) else none
  else if tag = 10010 then (Reject.decode bytes).map fun message => .reject message
  else if tag = 10027 then (RetransmitMeMessageResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.retransmitMeMessageResponse message) else none
  else if tag = 10009 then (RetransmitResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.retransmitResponse message) else none
  else if tag = 10033 then (RiskNotificationBroadcast.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.riskNotificationBroadcast message) else none
  else if tag = 10708 then (SrqsCreateDealNotification.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.srqsCreateDealNotification message) else none
  else if tag = 10709 then (SrqsDealNotification.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.srqsDealNotification message) else none
  else if tag = 10705 then (SrqsDealResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.srqsDealResponse message) else none
  else if tag = 10719 then (SrqsInquireSmartRespondentResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.srqsInquireSmartRespondentResponse message) else none
  else if tag = 10713 then (SrqsNegotiationNotification.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.srqsNegotiationNotification message) else none
  else if tag = 10712 then (SrqsNegotiationRequesterNotification.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.srqsNegotiationRequesterNotification message) else none
  else if tag = 10715 then (SrqsNegotiationStatusNotification.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.srqsNegotiationStatusNotification message) else none
  else if tag = 10711 then (SrqsOpenNegotiationNotification.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.srqsOpenNegotiationNotification message) else none
  else if tag = 10710 then (SrqsOpenNegotiationRequesterNotification.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.srqsOpenNegotiationRequesterNotification message) else none
  else if tag = 10707 then (SrqsQuoteNotification.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.srqsQuoteNotification message) else none
  else if tag = 10703 then (SrqsQuoteResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.srqsQuoteResponse message) else none
  else if tag = 10723 then (SrqsQuoteSnapshotNotification.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.srqsQuoteSnapshotNotification message) else none
  else if tag = 10722 then (SrqsResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.srqsResponse message) else none
  else if tag = 10714 then (SrqsStatusBroadcast.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.srqsStatusBroadcast message) else none
  else if tag = 10030 then (ServiceAvailabilityBroadcast.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.serviceAvailabilityBroadcast message) else none
  else if tag = 10044 then (ServiceAvailabilityMarketBroadcast.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.serviceAvailabilityMarketBroadcast message) else none
  else if tag = 10045 then (StatusBroadcast.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.statusBroadcast message) else none
  else if tag = 10005 then (SubscribeResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.subscribeResponse message) else none
  else if tag = 10607 then (TesApproveBroadcast.decode bytes).map fun message => .tesApproveBroadcast message
  else if tag = 10604 then (TesBroadcast.decode bytes).map fun message => .tesBroadcast message
  else if tag = 10606 then (TesDeleteBroadcast.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.tesDeleteBroadcast message) else none
  else if tag = 10610 then (TesExecutionBroadcast.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.tesExecutionBroadcast message) else none
  else if tag = 10611 then (TesResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.tesResponse message) else none
  else if tag = 10632 then (TesReversalBroadcast.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.tesReversalBroadcast message) else none
  else if tag = 10614 then (TesTradeBroadcast.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.tesTradeBroadcast message) else none
  else if tag = 10615 then (TesTradingSessionStatusBroadcast.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.tesTradingSessionStatusBroadcast message) else none
  else if tag = 10613 then (TesUploadBroadcast.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.tesUploadBroadcast message) else none
  else if tag = 10501 then (TmTradingSessionStatusBroadcast.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.tmTradingSessionStatusBroadcast message) else none
  else if tag = 10028 then (ThrottleUpdateNotification.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.throttleUpdateNotification message) else none
  else if tag = 10500 then (TradeBroadcast.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.tradeBroadcast message) else none
  else if tag = 10307 then (TradingSessionStatusBroadcast.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.tradingSessionStatusBroadcast message) else none
  else if tag = 10007 then (UnsubscribeResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.unsubscribeResponse message) else none
  else if tag = 10326 then (UpdateRemainingRiskAllowanceBaseResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.updateRemainingRiskAllowanceBaseResponse message) else none
  else if tag = 10019 then (UserLoginResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.userLoginResponse message) else none
  else if tag = 10024 then (UserLogoutResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.userLogoutResponse message) else none
  else none

theorem decode_encode (message : ServerPayload) :
    decode (tag message) (encode message) = some message := by
  cases message with
  | addComplexInstrumentResponse message => simp [decode, encode, tag, AddComplexInstrumentResponse.decode_encode_nil]
  | addFlexibleInstrumentResponse message => simp [decode, encode, tag, AddFlexibleInstrumentResponse.decode_encode_nil]
  | addScaledSimpleInstrumentResponse message => simp [decode, encode, tag, AddScaledSimpleInstrumentResponse.decode_encode_nil]
  | basketApproveBroadcast message => simp [decode, encode, tag, BasketApproveBroadcast.decode_encode_nil]
  | basketBroadcast message => simp [decode, encode, tag, BasketBroadcast.decode_encode_nil]
  | basketDeleteBroadcast message => simp [decode, encode, tag, BasketDeleteBroadcast.decode_encode_nil]
  | basketExecutionBroadcast message => simp [decode, encode, tag, BasketExecutionBroadcast.decode_encode_nil]
  | basketResponse message => simp [decode, encode, tag, BasketResponse.decode_encode_nil]
  | basketRollBroadcast message => simp [decode, encode, tag, BasketRollBroadcast.decode_encode_nil]
  | broadcastErrorNotification message => simp [decode, encode, tag, BroadcastErrorNotification.decode_encode]
  | clipDeletionNotification message => simp [decode, encode, tag, ClipDeletionNotification.decode_encode_nil]
  | clipExecutionNotification message => simp [decode, encode, tag, ClipExecutionNotification.decode_encode_nil]
  | clipResponse message => simp [decode, encode, tag, ClipResponse.decode_encode_nil]
  | crossRequestResponse message => simp [decode, encode, tag, CrossRequestResponse.decode_encode_nil]
  | deleteAllOrderBroadcast message => simp [decode, encode, tag, DeleteAllOrderBroadcast.decode_encode_nil]
  | deleteAllOrderNrResponse message => simp [decode, encode, tag, DeleteAllOrderNrResponse.decode_encode_nil]
  | deleteAllOrderQuoteEventBroadcast message => simp [decode, encode, tag, DeleteAllOrderQuoteEventBroadcast.decode_encode_nil]
  | deleteAllOrderResponse message => simp [decode, encode, tag, DeleteAllOrderResponse.decode_encode_nil]
  | deleteAllQuoteBroadcast message => simp [decode, encode, tag, DeleteAllQuoteBroadcast.decode_encode_nil]
  | deleteAllQuoteResponse message => simp [decode, encode, tag, DeleteAllQuoteResponse.decode_encode_nil]
  | deleteOrderBroadcast message => simp [decode, encode, tag, DeleteOrderBroadcast.decode_encode_nil]
  | deleteOrderNrResponse message => simp [decode, encode, tag, DeleteOrderNrResponse.decode_encode_nil]
  | deleteOrderResponse message => simp [decode, encode, tag, DeleteOrderResponse.decode_encode_nil]
  | forcedLogoutNotification message => simp [decode, encode, tag, ForcedLogoutNotification.decode_encode]
  | forcedUserLogoutNotification message => simp [decode, encode, tag, ForcedUserLogoutNotification.decode_encode]
  | heartbeatNotification message => simp [decode, encode, tag, HeartbeatNotification.decode_encode_nil]
  | inquireEnrichmentRuleIdListResponse message => simp [decode, encode, tag, InquireEnrichmentRuleIdListResponse.decode_encode_nil]
  | inquireMmParameterResponse message => simp [decode, encode, tag, InquireMmParameterResponse.decode_encode_nil]
  | inquireMarginBasedRiskLimitResponse message => simp [decode, encode, tag, InquireMarginBasedRiskLimitResponse.decode_encode_nil]
  | inquireSessionListResponse message => simp [decode, encode, tag, InquireSessionListResponse.decode_encode_nil]
  | inquireUserResponse message => simp [decode, encode, tag, InquireUserResponse.decode_encode_nil]
  | legalNotificationBroadcast message => simp [decode, encode, tag, LegalNotificationBroadcast.decode_encode]
  | logonResponse message => simp [decode, encode, tag, LogonResponse.decode_encode]
  | logoutResponse message => simp [decode, encode, tag, LogoutResponse.decode_encode_nil]
  | mmParameterDefinitionResponse message => simp [decode, encode, tag, MmParameterDefinitionResponse.decode_encode_nil]
  | massOrderAck message => simp [decode, encode, tag, MassOrderAck.decode_encode_nil]
  | massQuoteResponse message => simp [decode, encode, tag, MassQuoteResponse.decode_encode_nil]
  | modifyOrderNrResponse message => simp [decode, encode, tag, ModifyOrderNrResponse.decode_encode_nil]
  | modifyOrderResponse message => simp [decode, encode, tag, ModifyOrderResponse.decode_encode_nil]
  | newOrderNrResponse message => simp [decode, encode, tag, NewOrderNrResponse.decode_encode_nil]
  | newOrderResponse message => simp [decode, encode, tag, NewOrderResponse.decode_encode_nil]
  | newsBroadcast message => simp [decode, encode, tag, NewsBroadcast.decode_encode]
  | orderExecNotification message => simp [decode, encode, tag, OrderExecNotification.decode_encode_nil]
  | orderExecReportBroadcast message => simp [decode, encode, tag, OrderExecReportBroadcast.decode_encode_nil]
  | orderExecResponse message => simp [decode, encode, tag, OrderExecResponse.decode_encode_nil]
  | partyActionReport message => simp [decode, encode, tag, PartyActionReport.decode_encode_nil]
  | partyEntitlementsUpdateReport message => simp [decode, encode, tag, PartyEntitlementsUpdateReport.decode_encode_nil]
  | pingResponse message => simp [decode, encode, tag, PingResponse.decode_encode_nil]
  | preTradeRiskLimitResponse message => simp [decode, encode, tag, PreTradeRiskLimitResponse.decode_encode_nil]
  | quoteActivationNotification message => simp [decode, encode, tag, QuoteActivationNotification.decode_encode_nil]
  | quoteActivationResponse message => simp [decode, encode, tag, QuoteActivationResponse.decode_encode_nil]
  | quoteExecutionReport message => simp [decode, encode, tag, QuoteExecutionReport.decode_encode_nil]
  | rfqResponse message => simp [decode, encode, tag, RfqResponse.decode_encode_nil]
  | reject message => simp [decode, encode, tag, Reject.decode_encode]
  | retransmitMeMessageResponse message => simp [decode, encode, tag, RetransmitMeMessageResponse.decode_encode_nil]
  | retransmitResponse message => simp [decode, encode, tag, RetransmitResponse.decode_encode_nil]
  | riskNotificationBroadcast message => simp [decode, encode, tag, RiskNotificationBroadcast.decode_encode_nil]
  | srqsCreateDealNotification message => simp [decode, encode, tag, SrqsCreateDealNotification.decode_encode_nil]
  | srqsDealNotification message => simp [decode, encode, tag, SrqsDealNotification.decode_encode_nil]
  | srqsDealResponse message => simp [decode, encode, tag, SrqsDealResponse.decode_encode_nil]
  | srqsInquireSmartRespondentResponse message => simp [decode, encode, tag, SrqsInquireSmartRespondentResponse.decode_encode_nil]
  | srqsNegotiationNotification message => simp [decode, encode, tag, SrqsNegotiationNotification.decode_encode_nil]
  | srqsNegotiationRequesterNotification message => simp [decode, encode, tag, SrqsNegotiationRequesterNotification.decode_encode_nil]
  | srqsNegotiationStatusNotification message => simp [decode, encode, tag, SrqsNegotiationStatusNotification.decode_encode_nil]
  | srqsOpenNegotiationNotification message => simp [decode, encode, tag, SrqsOpenNegotiationNotification.decode_encode_nil]
  | srqsOpenNegotiationRequesterNotification message => simp [decode, encode, tag, SrqsOpenNegotiationRequesterNotification.decode_encode_nil]
  | srqsQuoteNotification message => simp [decode, encode, tag, SrqsQuoteNotification.decode_encode_nil]
  | srqsQuoteResponse message => simp [decode, encode, tag, SrqsQuoteResponse.decode_encode_nil]
  | srqsQuoteSnapshotNotification message => simp [decode, encode, tag, SrqsQuoteSnapshotNotification.decode_encode_nil]
  | srqsResponse message => simp [decode, encode, tag, SrqsResponse.decode_encode_nil]
  | srqsStatusBroadcast message => simp [decode, encode, tag, SrqsStatusBroadcast.decode_encode_nil]
  | serviceAvailabilityBroadcast message => simp [decode, encode, tag, ServiceAvailabilityBroadcast.decode_encode_nil]
  | serviceAvailabilityMarketBroadcast message => simp [decode, encode, tag, ServiceAvailabilityMarketBroadcast.decode_encode_nil]
  | statusBroadcast message => simp [decode, encode, tag, StatusBroadcast.decode_encode_nil]
  | subscribeResponse message => simp [decode, encode, tag, SubscribeResponse.decode_encode_nil]
  | tesApproveBroadcast message => simp [decode, encode, tag, TesApproveBroadcast.decode_encode]
  | tesBroadcast message => simp [decode, encode, tag, TesBroadcast.decode_encode]
  | tesDeleteBroadcast message => simp [decode, encode, tag, TesDeleteBroadcast.decode_encode_nil]
  | tesExecutionBroadcast message => simp [decode, encode, tag, TesExecutionBroadcast.decode_encode_nil]
  | tesResponse message => simp [decode, encode, tag, TesResponse.decode_encode_nil]
  | tesReversalBroadcast message => simp [decode, encode, tag, TesReversalBroadcast.decode_encode_nil]
  | tesTradeBroadcast message => simp [decode, encode, tag, TesTradeBroadcast.decode_encode_nil]
  | tesTradingSessionStatusBroadcast message => simp [decode, encode, tag, TesTradingSessionStatusBroadcast.decode_encode_nil]
  | tesUploadBroadcast message => simp [decode, encode, tag, TesUploadBroadcast.decode_encode_nil]
  | tmTradingSessionStatusBroadcast message => simp [decode, encode, tag, TmTradingSessionStatusBroadcast.decode_encode_nil]
  | throttleUpdateNotification message => simp [decode, encode, tag, ThrottleUpdateNotification.decode_encode_nil]
  | tradeBroadcast message => simp [decode, encode, tag, TradeBroadcast.decode_encode_nil]
  | tradingSessionStatusBroadcast message => simp [decode, encode, tag, TradingSessionStatusBroadcast.decode_encode_nil]
  | unsubscribeResponse message => simp [decode, encode, tag, UnsubscribeResponse.decode_encode_nil]
  | updateRemainingRiskAllowanceBaseResponse message => simp [decode, encode, tag, UpdateRemainingRiskAllowanceBaseResponse.decode_encode_nil]
  | userLoginResponse message => simp [decode, encode, tag, UserLoginResponse.decode_encode_nil]
  | userLogoutResponse message => simp [decode, encode, tag, UserLogoutResponse.decode_encode_nil]

end ServerPayload

/-- Server Message -/
structure ServerMessage where
  serverPayload : ServerPayload
  deriving DecidableEq, Repr

namespace ServerMessage

def encodeBody (message : ServerMessage) : List UInt8 :=
  encodeUIntLE 2 (ServerPayload.tag message.serverPayload)
    ++ ServerPayload.encode message.serverPayload

def decodeBody (bytes : List UInt8) : Option ServerMessage := do
  let (templateId, bytes) ← decodeUIntLE 2 bytes
  let serverPayload ← ServerPayload.decode templateId bytes
  pure { serverPayload }

theorem decodeBody_encodeBody (message : ServerMessage) : decodeBody (encodeBody message) = some message := by
  unfold decodeBody encodeBody
  simp only [Option.bind_eq_bind]
  rw [decodeUIntLE_encodeUIntLE]
  simp only [Option.bind_some]
  rw [ServerPayload.decode_encode, Option.bind_some]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : ServerMessage) : (encodeBody message).length + 4 < 256 ^ 4 := by
  unfold encodeBody
  cases message.serverPayload with
  | addComplexInstrumentResponse inner =>
    have bound_inner := AddComplexInstrumentResponse.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | addFlexibleInstrumentResponse inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, AddFlexibleInstrumentResponse.encode_length]
    omega
  | addScaledSimpleInstrumentResponse inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, AddScaledSimpleInstrumentResponse.encode_length]
    omega
  | basketApproveBroadcast inner =>
    have bound_inner := BasketApproveBroadcast.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | basketBroadcast inner =>
    have bound_inner := BasketBroadcast.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | basketDeleteBroadcast inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, BasketDeleteBroadcast.encode_length]
    omega
  | basketExecutionBroadcast inner =>
    have bound_inner := BasketExecutionBroadcast.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | basketResponse inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, BasketResponse.encode_length]
    omega
  | basketRollBroadcast inner =>
    have bound_inner := BasketRollBroadcast.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | broadcastErrorNotification inner =>
    have bound_inner := BroadcastErrorNotification.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | clipDeletionNotification inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, ClipDeletionNotification.encode_length]
    omega
  | clipExecutionNotification inner =>
    have bound_inner := ClipExecutionNotification.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | clipResponse inner =>
    have bound_inner := ClipResponse.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | crossRequestResponse inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, CrossRequestResponse.encode_length]
    omega
  | deleteAllOrderBroadcast inner =>
    have bound_inner := DeleteAllOrderBroadcast.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | deleteAllOrderNrResponse inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, DeleteAllOrderNrResponse.encode_length]
    omega
  | deleteAllOrderQuoteEventBroadcast inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, DeleteAllOrderQuoteEventBroadcast.encode_length]
    omega
  | deleteAllOrderResponse inner =>
    have bound_inner := DeleteAllOrderResponse.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | deleteAllQuoteBroadcast inner =>
    have bound_inner := DeleteAllQuoteBroadcast.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | deleteAllQuoteResponse inner =>
    have bound_inner := DeleteAllQuoteResponse.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | deleteOrderBroadcast inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, DeleteOrderBroadcast.encode_length]
    omega
  | deleteOrderNrResponse inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, DeleteOrderNrResponse.encode_length]
    omega
  | deleteOrderResponse inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, DeleteOrderResponse.encode_length]
    omega
  | forcedLogoutNotification inner =>
    have bound_inner := ForcedLogoutNotification.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | forcedUserLogoutNotification inner =>
    have bound_inner := ForcedUserLogoutNotification.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | heartbeatNotification inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, HeartbeatNotification.encode_length]
    omega
  | inquireEnrichmentRuleIdListResponse inner =>
    have bound_inner := InquireEnrichmentRuleIdListResponse.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | inquireMmParameterResponse inner =>
    have bound_inner := InquireMmParameterResponse.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | inquireMarginBasedRiskLimitResponse inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, InquireMarginBasedRiskLimitResponse.encode_length]
    omega
  | inquireSessionListResponse inner =>
    have bound_inner := InquireSessionListResponse.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | inquireUserResponse inner =>
    have bound_inner := InquireUserResponse.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | legalNotificationBroadcast inner =>
    have bound_inner := LegalNotificationBroadcast.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | logonResponse inner =>
    have bound_inner := LogonResponse.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | logoutResponse inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, LogoutResponse.encode_length]
    omega
  | mmParameterDefinitionResponse inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, MmParameterDefinitionResponse.encode_length]
    omega
  | massOrderAck inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, MassOrderAck.encode_length]
    omega
  | massQuoteResponse inner =>
    have bound_inner := MassQuoteResponse.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | modifyOrderNrResponse inner =>
    have bound_inner := ModifyOrderNrResponse.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | modifyOrderResponse inner =>
    have bound_inner := ModifyOrderResponse.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | newOrderNrResponse inner =>
    have bound_inner := NewOrderNrResponse.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | newOrderResponse inner =>
    have bound_inner := NewOrderResponse.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | newsBroadcast inner =>
    have bound_inner := NewsBroadcast.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | orderExecNotification inner =>
    have bound_inner := OrderExecNotification.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | orderExecReportBroadcast inner =>
    have bound_inner := OrderExecReportBroadcast.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | orderExecResponse inner =>
    have bound_inner := OrderExecResponse.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | partyActionReport inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, PartyActionReport.encode_length]
    omega
  | partyEntitlementsUpdateReport inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, PartyEntitlementsUpdateReport.encode_length]
    omega
  | pingResponse inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, PingResponse.encode_length]
    omega
  | preTradeRiskLimitResponse inner =>
    have bound_inner := PreTradeRiskLimitResponse.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | quoteActivationNotification inner =>
    have bound_inner := QuoteActivationNotification.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | quoteActivationResponse inner =>
    have bound_inner := QuoteActivationResponse.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | quoteExecutionReport inner =>
    have bound_inner := QuoteExecutionReport.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | rfqResponse inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, RfqResponse.encode_length]
    omega
  | reject inner =>
    have bound_inner := Reject.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | retransmitMeMessageResponse inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, RetransmitMeMessageResponse.encode_length]
    omega
  | retransmitResponse inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, RetransmitResponse.encode_length]
    omega
  | riskNotificationBroadcast inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, RiskNotificationBroadcast.encode_length]
    omega
  | srqsCreateDealNotification inner =>
    have bound_inner := SrqsCreateDealNotification.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | srqsDealNotification inner =>
    have bound_inner := SrqsDealNotification.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | srqsDealResponse inner =>
    have bound_inner := SrqsDealResponse.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | srqsInquireSmartRespondentResponse inner =>
    have bound_inner := SrqsInquireSmartRespondentResponse.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | srqsNegotiationNotification inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, SrqsNegotiationNotification.encode_length]
    omega
  | srqsNegotiationRequesterNotification inner =>
    have bound_inner := SrqsNegotiationRequesterNotification.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | srqsNegotiationStatusNotification inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, SrqsNegotiationStatusNotification.encode_length]
    omega
  | srqsOpenNegotiationNotification inner =>
    have bound_inner := SrqsOpenNegotiationNotification.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | srqsOpenNegotiationRequesterNotification inner =>
    have bound_inner := SrqsOpenNegotiationRequesterNotification.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | srqsQuoteNotification inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, SrqsQuoteNotification.encode_length]
    omega
  | srqsQuoteResponse inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, SrqsQuoteResponse.encode_length]
    omega
  | srqsQuoteSnapshotNotification inner =>
    have bound_inner := SrqsQuoteSnapshotNotification.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | srqsResponse inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, SrqsResponse.encode_length]
    omega
  | srqsStatusBroadcast inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, SrqsStatusBroadcast.encode_length]
    omega
  | serviceAvailabilityBroadcast inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, ServiceAvailabilityBroadcast.encode_length]
    omega
  | serviceAvailabilityMarketBroadcast inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, ServiceAvailabilityMarketBroadcast.encode_length]
    omega
  | statusBroadcast inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, StatusBroadcast.encode_length]
    omega
  | subscribeResponse inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, SubscribeResponse.encode_length]
    omega
  | tesApproveBroadcast inner =>
    have bound_inner := TesApproveBroadcast.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | tesBroadcast inner =>
    have bound_inner := TesBroadcast.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | tesDeleteBroadcast inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, TesDeleteBroadcast.encode_length]
    omega
  | tesExecutionBroadcast inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, TesExecutionBroadcast.encode_length]
    omega
  | tesResponse inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, TesResponse.encode_length]
    omega
  | tesReversalBroadcast inner =>
    have bound_inner := TesReversalBroadcast.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | tesTradeBroadcast inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, TesTradeBroadcast.encode_length]
    omega
  | tesTradingSessionStatusBroadcast inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, TesTradingSessionStatusBroadcast.encode_length]
    omega
  | tesUploadBroadcast inner =>
    have bound_inner := TesUploadBroadcast.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | tmTradingSessionStatusBroadcast inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, TmTradingSessionStatusBroadcast.encode_length]
    omega
  | throttleUpdateNotification inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, ThrottleUpdateNotification.encode_length]
    omega
  | tradeBroadcast inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, TradeBroadcast.encode_length]
    omega
  | tradingSessionStatusBroadcast inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, TradingSessionStatusBroadcast.encode_length]
    omega
  | unsubscribeResponse inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, UnsubscribeResponse.encode_length]
    omega
  | updateRemainingRiskAllowanceBaseResponse inner =>
    have bound_inner := UpdateRemainingRiskAllowanceBaseResponse.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | userLoginResponse inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, UserLoginResponse.encode_length]
    omega
  | userLogoutResponse inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, UserLogoutResponse.encode_length]
    omega

/-- Size rule: Body Len counts the bytes after it plus 4, so it is written from the body and checked on decode -/
def encode : ServerMessage → List UInt8 :=
  encodeFramedLE 4 4 encodeBody

def decode : List UInt8 → Option (ServerMessage × List UInt8) :=
  decodeFramedAllLE 4 4 decodeBody

@[simp] theorem decode_encode (message : ServerMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramedAllLE_encodeFramedLE 4 4 encodeBody decodeBody decodeBody_encodeBody encodeBody_length_lt message rest

theorem encode_length_pos (message : ServerMessage) : (encode message).length > 0 := by
  unfold encode
  rw [encodeFramedLE_length]
  omega

end ServerMessage

/-- Server Packet -/
structure ServerPacket where
  serverMessage : List ServerMessage
  deriving DecidableEq, Repr

namespace ServerPacket

def encode (message : ServerPacket) : List UInt8 :=
  encodeMany ServerMessage.encode message.serverMessage

def decode (bytes : List UInt8) : Option ServerPacket := do
  let serverMessage ← decodeAll ServerMessage.decode bytes.length bytes
  pure { serverMessage }

theorem decode_encode (message : ServerPacket) : decode (encode message) = some message := by
  unfold decode encode
  simp only [Option.bind_eq_bind]
  rw [decodeAll_encodeMany ServerMessage.encode ServerMessage.decode ServerMessage.decode_encode ServerMessage.encode_length_pos message.serverMessage _ (encodeMany_length_ge ServerMessage.encode ServerMessage.encode_length_pos message.serverMessage), Option.bind_some]
  rfl

end ServerPacket

end Omi.EurexT7EtiFbeV140Server
