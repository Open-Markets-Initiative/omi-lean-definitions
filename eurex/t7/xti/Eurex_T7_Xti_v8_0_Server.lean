import Omi.Wire

/-!
# Eurex Exchange Cash Enhanced Trading Interface v8.0

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Best Quote Execution Report is not framed: its length Body Len is not an integer it reads.

Note: Best Quote Response is not framed: its length Body Len is not an integer it reads.

Note: Alignment Padding pads to a 8 byte boundary: it is read as the bytes left to the end of the frame, fewer than 8, and the frame's length is trusted to keep the boundary.

Note: Broadcast Error Notification is not framed: its length Body Len is not an integer it reads.

Note: Cross Request Response is not framed: its length Body Len is not an integer it reads.

Note: Delete All Order Broadcast is not framed: its length Body Len is not an integer it reads.

Note: Delete All Order Nr Response is not framed: its length Body Len is not an integer it reads.

Note: Delete All Order Quote Event Broadcast is not framed: its length Body Len is not an integer it reads.

Note: Delete All Order Response is not framed: its length Body Len is not an integer it reads.

Note: Delete All Quote Broadcast is not framed: its length Body Len is not an integer it reads.

Note: Delete All Quote Response is not framed: its length Body Len is not an integer it reads.

Note: Delete Order Broadcast is not framed: its length Body Len is not an integer it reads.

Note: Delete Order Nr Response is not framed: its length Body Len is not an integer it reads.

Note: Delete Order Response is not framed: its length Body Len is not an integer it reads.

Note: Extended Deletion Report is not framed: its length Body Len is not an integer it reads.

Note: Alignment Padding pads to a 8 byte boundary: it is read as the bytes left to the end of the frame, fewer than 8, and the frame's length is trusted to keep the boundary.

Note: Forced Logout Notification is not framed: its length Body Len is not an integer it reads.

Note: Alignment Padding pads to a 8 byte boundary: it is read as the bytes left to the end of the frame, fewer than 8, and the frame's length is trusted to keep the boundary.

Note: Forced User Logout Notification is not framed: its length Body Len is not an integer it reads.

Note: Heartbeat Notification is not framed: its length Body Len is not an integer it reads.

Note: Inquire Enrichment Rule Id List Response is not framed: its length Body Len is not an integer it reads.

Note: Inquire Session List Response is not framed: its length Body Len is not an integer it reads.

Note: Inquire User Response is not framed: its length Body Len is not an integer it reads.

Note: Issuer Notification is not framed: its length Body Len is not an integer it reads.

Note: Issuer Security State Change Response is not framed: its length Body Len is not an integer it reads.

Note: Alignment Padding pads to a 8 byte boundary: it is read as the bytes left to the end of the frame, fewer than 8, and the frame's length is trusted to keep the boundary.

Note: Legal Notification Broadcast is not framed: its length Body Len is not an integer it reads.

Note: Logon Response is not framed: its length Body Len is not an integer it reads.

Note: Logout Response is not framed: its length Body Len is not an integer it reads.

Note: Mass Quote Response is not framed: its length Body Len is not an integer it reads.

Note: Modify Order Nr Response is not framed: its length Body Len is not an integer it reads.

Note: Modify Order Response is not framed: its length Body Len is not an integer it reads.

Note: New Order Nr Response is not framed: its length Body Len is not an integer it reads.

Note: New Order Response is not framed: its length Body Len is not an integer it reads.

Note: Alignment Padding pads to a 8 byte boundary: it is read as the bytes left to the end of the frame, fewer than 8, and the frame's length is trusted to keep the boundary.

Note: News Broadcast is not framed: its length Body Len is not an integer it reads.

Note: Order Exec Notification is not framed: its length Body Len is not an integer it reads.

Note: Order Exec Report Broadcast is not framed: its length Body Len is not an integer it reads.

Note: Order Exec Response is not framed: its length Body Len is not an integer it reads.

Note: Party Action Report is not framed: its length Body Len is not an integer it reads.

Note: Party Entitlements Update Report is not framed: its length Body Len is not an integer it reads.

Note: Quote Activation Notification is not framed: its length Body Len is not an integer it reads.

Note: Quote Activation Response is not framed: its length Body Len is not an integer it reads.

Note: Quote Execution Report is not framed: its length Body Len is not an integer it reads.

Note: Rfq Broadcast is not framed: its length Body Len is not an integer it reads.

Note: Rfq Reject Notification is not framed: its length Body Len is not an integer it reads.

Note: Rfq Response is not framed: its length Body Len is not an integer it reads.

Note: Rfq Specialist Broadcast is not framed: its length Body Len is not an integer it reads.

Note: Alignment Padding pads to a 8 byte boundary: it is read as the bytes left to the end of the frame, fewer than 8, and the frame's length is trusted to keep the boundary.

Note: Reject is not framed: its length Body Len is not an integer it reads.

Note: Retransmit Me Message Response is not framed: its length Body Len is not an integer it reads.

Note: Retransmit Response is not framed: its length Body Len is not an integer it reads.

Note: Service Availability Broadcast is not framed: its length Body Len is not an integer it reads.

Note: Service Availability Market Broadcast is not framed: its length Body Len is not an integer it reads.

Note: Specialist Delete All Order Broadcast is not framed: its length Body Len is not an integer it reads.

Note: Specialist Instrument Event Notification is not framed: its length Body Len is not an integer it reads.

Note: Specialist Order Book Notification is not framed: its length Body Len is not an integer it reads.

Note: Specialist Rfq Reply Notification is not framed: its length Body Len is not an integer it reads.

Note: Specialist Rfq Reply Response is not framed: its length Body Len is not an integer it reads.

Note: Specialist Security State Change Response is not framed: its length Body Len is not an integer it reads.

Note: Subscribe Response is not framed: its length Body Len is not an integer it reads.

Note: Tes Approve Broadcast is not framed: its length Body Len is not an integer it reads.

Note: Tes Broadcast is not framed: its length Body Len is not an integer it reads.

Note: Tes Delete Broadcast is not framed: its length Body Len is not an integer it reads.

Note: Tes Execution Broadcast is not framed: its length Body Len is not an integer it reads.

Note: Tes Response is not framed: its length Body Len is not an integer it reads.

Note: Tes Trade Broadcast is not framed: its length Body Len is not an integer it reads.

Note: Tes Trading Session Status Broadcast is not framed: its length Body Len is not an integer it reads.

Note: Tm Trading Session Status Broadcast is not framed: its length Body Len is not an integer it reads.

Note: Throttle Update Notification is not framed: its length Body Len is not an integer it reads.

Note: Trade Broadcast is not framed: its length Body Len is not an integer it reads.

Note: Trading Session Status Broadcast is not framed: its length Body Len is not an integer it reads.

Note: Trailing Stop Update Notification is not framed: its length Body Len is not an integer it reads.

Note: Unsubscribe Response is not framed: its length Body Len is not an integer it reads.

Note: User Login Response is not framed: its length Body Len is not an integer it reads.

Note: User Logout Response is not framed: its length Body Len is not an integer it reads.

Note: Xetra En Light Create Deal Notification is not framed: its length Body Len is not an integer it reads.

Note: Xetra En Light Deal Response is not framed: its length Body Len is not an integer it reads.

Note: Xetra En Light Negotiation Notification is not framed: its length Body Len is not an integer it reads.

Note: Xetra En Light Negotiation Requester Notification is not framed: its length Body Len is not an integer it reads.

Note: Xetra En Light Negotiation Status Notification is not framed: its length Body Len is not an integer it reads.

Note: Xetra En Light Open Negotiation Notification is not framed: its length Body Len is not an integer it reads.

Note: Xetra En Light Open Negotiation Requester Notification is not framed: its length Body Len is not an integer it reads.

Note: Xetra En Light Quote Notification is not framed: its length Body Len is not an integer it reads.

Note: Xetra En Light Quote Requester Notification is not framed: its length Body Len is not an integer it reads.

Note: Xetra En Light Quote Response is not framed: its length Body Len is not an integer it reads.

Note: Xetra En Light Status Broadcast is not framed: its length Body Len is not an integer it reads.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.EurexT7XtiFbeV80Server

/-- Ord Status: one byte code -/
def OrdStatus.codes : List UInt8 :=
  [0x30, 0x31, 0x32, 0x34, 0x36, 0x39, 0x41, 0x45]

inductive OrdStatus where
  | new -- New
  | partiallyfilled -- Partiallyfilled
  | filled -- Filled
  | canceled -- Canceled
  | pendingCancel -- Pending Cancel
  | suspended -- Suspended
  | pendingNew -- Pending New
  | pendingReplace -- Pending Replace
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
  | .pendingNew => 0x41
  | .pendingReplace => 0x45
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : OrdStatus :=
  if byte = 0x30 then .new
  else if byte = 0x31 then .partiallyfilled
  else if byte = 0x32 then .filled
  else if byte = 0x34 then .canceled
  else if byte = 0x36 then .pendingCancel
  else if byte = 0x39 then .suspended
  else if byte = 0x41 then .pendingNew
  else .pendingReplace

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
  | pendingNew => decide
  | pendingReplace => decide
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
  [0x30, 0x34, 0x35, 0x36, 0x39, 0x44, 0x4C, 0x46, 0x41, 0x45]

inductive ExecType where
  | new -- New
  | canceled -- Canceled
  | replaced -- Replaced
  | pendingCancele -- Pending Cancele
  | suspended -- Suspended
  | restated -- Restated
  | triggered -- Triggered
  | trade -- Trade
  | pendingNew -- Pending New
  | pendingReplace -- Pending Replace
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
  | .pendingNew => 0x41
  | .pendingReplace => 0x45
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
  else if byte = 0x46 then .trade
  else if byte = 0x41 then .pendingNew
  else .pendingReplace

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
  | pendingNew => decide
  | pendingReplace => decide
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
    ++ (encodeUIntLE 8 message.notificationIn
    ++ (encodeUIntLE 8 message.sendingTime
    ++ (encodeUIntLE 4 message.applSubId
    ++ (encodeUIntLE 2 message.partitionId
    ++ (Alpha.encode message.applMsgId
    ++ (encodeUInt 1 message.applId
    ++ (encodeUInt 1 message.applResendFlag
    ++ (encodeUInt 1 message.lastFragment
    ++ (Alpha.encode message.pad7)))))))))

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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end RbcHeaderMeComp

/-- Best Quote Execution Report: 122 bytes -/
structure BestQuoteExecutionReport where
  pad2 : Alpha 2
  rbcHeaderMeComp : RbcHeaderMeComp
  execId : BitVec 64
  quoteMsgId : BitVec 64
  securityId : BitVec 64
  quoteEventPx : BitVec 64
  quoteEventQty : BitVec 64
  reservedSize : BitVec 64
  marketSegmentId : BitVec 32
  quoteEventMatchId : BitVec 32
  quoteEventExecId : BitVec 32
  quoteEventType : BitVec 8
  quoteEventSide : BitVec 8
  pad2v2 : Alpha 2
  deriving DecidableEq, Repr

namespace BestQuoteExecutionReport

def encode (message : BestQuoteExecutionReport) : List UInt8 :=
  Alpha.encode message.pad2
    ++ (RbcHeaderMeComp.encode message.rbcHeaderMeComp
    ++ (encodeUIntLE 8 message.execId
    ++ (encodeUIntLE 8 message.quoteMsgId
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.quoteEventPx
    ++ (encodeUIntLE 8 message.quoteEventQty
    ++ (encodeUIntLE 8 message.reservedSize
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.quoteEventMatchId
    ++ (encodeUIntLE 4 message.quoteEventExecId
    ++ (encodeUInt 1 message.quoteEventType
    ++ (encodeUInt 1 message.quoteEventSide
    ++ (Alpha.encode message.pad2v2)))))))))))))

def decode (bytes : List UInt8) : Option (BestQuoteExecutionReport × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderMeComp, bytes) ← RbcHeaderMeComp.decode bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  let (quoteMsgId, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (quoteEventPx, bytes) ← decodeUIntLE 8 bytes
  let (quoteEventQty, bytes) ← decodeUIntLE 8 bytes
  let (reservedSize, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (quoteEventMatchId, bytes) ← decodeUIntLE 4 bytes
  let (quoteEventExecId, bytes) ← decodeUIntLE 4 bytes
  let (quoteEventType, bytes) ← decodeUInt 1 bytes
  let (quoteEventSide, bytes) ← decodeUInt 1 bytes
  let (pad2v2, bytes) ← Alpha.decode 2 bytes
  pure ({ pad2, rbcHeaderMeComp, execId, quoteMsgId, securityId, quoteEventPx, quoteEventQty, reservedSize, marketSegmentId, quoteEventMatchId, quoteEventExecId, quoteEventType, quoteEventSide, pad2v2 }, bytes)

@[simp] theorem encode_length (message : BestQuoteExecutionReport) : (encode message).length = 122 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RbcHeaderMeComp.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : BestQuoteExecutionReport) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BestQuoteExecutionReport) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RbcHeaderMeComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
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

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : BestQuoteExecutionReport) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end BestQuoteExecutionReport

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
    ++ (encodeUIntLE 8 message.trdRegTsTimeIn
    ++ (encodeUIntLE 8 message.trdRegTsTimeOut
    ++ (encodeUIntLE 8 message.responseIn
    ++ (encodeUIntLE 8 message.sendingTime
    ++ (encodeUIntLE 4 message.msgSeqNum
    ++ (encodeUInt 1 message.lastFragment
    ++ (Alpha.encode message.pad3)))))))

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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
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

end NrResponseHeaderMeComp

/-- Best Quote Response: 98 bytes -/
structure BestQuoteResponse where
  pad2 : Alpha 2
  nrResponseHeaderMeComp : NrResponseHeaderMeComp
  quoteId : BitVec 64
  quoteResponseId : BitVec 64
  securityId : BitVec 64
  bidCxlSize : BitVec 64
  offerCxlSize : BitVec 64
  marketSegmentId : BitVec 32
  pad4 : Alpha 4
  deriving DecidableEq, Repr

namespace BestQuoteResponse

def encode (message : BestQuoteResponse) : List UInt8 :=
  Alpha.encode message.pad2
    ++ (NrResponseHeaderMeComp.encode message.nrResponseHeaderMeComp
    ++ (encodeUIntLE 8 message.quoteId
    ++ (encodeUIntLE 8 message.quoteResponseId
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.bidCxlSize
    ++ (encodeUIntLE 8 message.offerCxlSize
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (Alpha.encode message.pad4))))))))

def decode (bytes : List UInt8) : Option (BestQuoteResponse × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (nrResponseHeaderMeComp, bytes) ← NrResponseHeaderMeComp.decode bytes
  let (quoteId, bytes) ← decodeUIntLE 8 bytes
  let (quoteResponseId, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (bidCxlSize, bytes) ← decodeUIntLE 8 bytes
  let (offerCxlSize, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (pad4, bytes) ← Alpha.decode 4 bytes
  pure ({ pad2, nrResponseHeaderMeComp, quoteId, quoteResponseId, securityId, bidCxlSize, offerCxlSize, marketSegmentId, pad4 }, bytes)

@[simp] theorem encode_length (message : BestQuoteResponse) : (encode message).length = 98 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, NrResponseHeaderMeComp.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : BestQuoteResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BestQuoteResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NrResponseHeaderMeComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
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

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : BestQuoteResponse) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end BestQuoteResponse

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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
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
  pad4 : Alpha 4
  varText : Bounded 2 UInt8
  alignmentPadding : Capped 7
  deriving DecidableEq, Repr

namespace BroadcastErrorNotification

def encode (message : BroadcastErrorNotification) : List UInt8 :=
  Alpha.encode message.pad2
    ++ (NotifHeaderComp.encode message.notifHeaderComp
    ++ (encodeUIntLE 4 message.applIdStatus
    ++ (encodeUIntLE 4 message.refApplSubId
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.varText.val.length)
    ++ (encodeUInt 1 message.refApplId
    ++ (encodeUInt 1 message.sessionStatus
    ++ (Alpha.encode message.pad4
    ++ (encodeMany Byte.encode message.varText.val
    ++ (message.alignmentPadding.val)))))))))

def decode (bytes : List UInt8) : Option BroadcastErrorNotification := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (notifHeaderComp, bytes) ← NotifHeaderComp.decode bytes
  let (applIdStatus, bytes) ← decodeUIntLE 4 bytes
  let (refApplSubId, bytes) ← decodeUIntLE 4 bytes
  let (varTextLen, bytes) ← decodeUIntLE 2 bytes
  let (refApplId, bytes) ← decodeUInt 1 bytes
  let (sessionStatus, bytes) ← decodeUInt 1 bytes
  let (pad4, bytes) ← Alpha.decode 4 bytes
  let (varText_, bytes) ← decodeMany Byte.decode varTextLen.toNat bytes
  let alignmentPadding_ := bytes
  if fits_varText : varText_.length < 256 ^ 2 then
    if fits_alignmentPadding : alignmentPadding_.length ≤ 7 then
      pure { pad2, notifHeaderComp, applIdStatus, refApplSubId, refApplId, sessionStatus, pad4, varText := ⟨varText_, fits_varText⟩, alignmentPadding := ⟨alignmentPadding_, fits_alignmentPadding⟩ }
    else none
  else none

theorem encode_length_pos (message : BroadcastErrorNotification) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : BroadcastErrorNotification) : (encode message).length ≤ 65568 := by
  have bound_varText := message.varText.length_lt
  have bound_alignmentPadding := message.alignmentPadding.length_le
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, NotifHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const Byte.encode 1 Byte.encode_length]
  omega

theorem decode_encode (message : BroadcastErrorNotification) : decode (encode message) = some message := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  dsimp only
  rw [NotifHeaderComp.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 Byte.encode Byte.decode Byte.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.varText.length_lt, dite_eq_left message.alignmentPadding.length_le]
  rfl

end BroadcastErrorNotification

/-- Cross Request Response: 58 bytes -/
structure CrossRequestResponse where
  pad2 : Alpha 2
  nrResponseHeaderMeComp : NrResponseHeaderMeComp
  execId : BitVec 64
  deriving DecidableEq, Repr

namespace CrossRequestResponse

def encode (message : CrossRequestResponse) : List UInt8 :=
  Alpha.encode message.pad2
    ++ (NrResponseHeaderMeComp.encode message.nrResponseHeaderMeComp
    ++ (encodeUIntLE 8 message.execId))

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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NrResponseHeaderMeComp.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : CrossRequestResponse) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end CrossRequestResponse

/-- Not Affected Orders Grp Comp: 16 bytes -/
structure NotAffectedOrdersGrpComp where
  notAffectedOrderId : BitVec 64
  notAffOrigClOrdId : BitVec 64
  deriving DecidableEq, Repr

namespace NotAffectedOrdersGrpComp

def encode (message : NotAffectedOrdersGrpComp) : List UInt8 :=
  encodeUIntLE 8 message.notAffectedOrderId
    ++ (encodeUIntLE 8 message.notAffOrigClOrdId)

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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end NotAffectedOrdersGrpComp

/-- Affected Ord Grp Comp: 16 bytes -/
structure AffectedOrdGrpComp where
  affectedOrderId : BitVec 64
  affectedOrigClOrdId : BitVec 64
  deriving DecidableEq, Repr

namespace AffectedOrdGrpComp

def encode (message : AffectedOrdGrpComp) : List UInt8 :=
  encodeUIntLE 8 message.affectedOrderId
    ++ (encodeUIntLE 8 message.affectedOrigClOrdId)

def decode (bytes : List UInt8) : Option (AffectedOrdGrpComp × List UInt8) := do
  let (affectedOrderId, bytes) ← decodeUIntLE 8 bytes
  let (affectedOrigClOrdId, bytes) ← decodeUIntLE 8 bytes
  pure ({ affectedOrderId, affectedOrigClOrdId }, bytes)

@[simp] theorem encode_length (message : AffectedOrdGrpComp) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length]

theorem encode_length_pos (message : AffectedOrdGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AffectedOrdGrpComp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

end AffectedOrdGrpComp

/-- Affected Order Requests Grp Comp: 8 bytes -/
structure AffectedOrderRequestsGrpComp where
  affectedOrderRequestId : BitVec 32
  pad4 : Alpha 4
  deriving DecidableEq, Repr

namespace AffectedOrderRequestsGrpComp

def encode (message : AffectedOrderRequestsGrpComp) : List UInt8 :=
  encodeUIntLE 4 message.affectedOrderRequestId
    ++ (Alpha.encode message.pad4)

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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
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
  pad6 : Alpha 6
  notAffectedOrdersGrpComp : Bounded 2 NotAffectedOrdersGrpComp
  affectedOrdGrpComp : Bounded 2 AffectedOrdGrpComp
  affectedOrderRequestsGrpComp : Bounded 2 AffectedOrderRequestsGrpComp
  deriving DecidableEq, Repr

namespace DeleteAllOrderBroadcast

def encode (message : DeleteAllOrderBroadcast) : List UInt8 :=
  Alpha.encode message.pad2
    ++ (RbcHeaderMeComp.encode message.rbcHeaderMeComp
    ++ (encodeUIntLE 8 message.massActionReportId
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.targetPartyIdSessionId
    ++ (encodeUIntLE 4 message.targetPartyIdExecutingTrader
    ++ (encodeUIntLE 4 message.partyIdEnteringTrader
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.notAffectedOrdersGrpComp.val.length)
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.affectedOrdGrpComp.val.length)
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.affectedOrderRequestsGrpComp.val.length)
    ++ (encodeUInt 1 message.partyIdEnteringFirm
    ++ (encodeUInt 1 message.massActionReason
    ++ (encodeUInt 1 message.execInst
    ++ (encodeUInt 1 message.side
    ++ (Alpha.encode message.pad6
    ++ (encodeMany NotAffectedOrdersGrpComp.encode message.notAffectedOrdersGrpComp.val
    ++ (encodeMany AffectedOrdGrpComp.encode message.affectedOrdGrpComp.val
    ++ (encodeMany AffectedOrderRequestsGrpComp.encode message.affectedOrderRequestsGrpComp.val)))))))))))))))))))

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
  let (noAffectedOrders, bytes) ← decodeUIntLE 2 bytes
  let (noAffectedOrderRequests, bytes) ← decodeUIntLE 2 bytes
  let (partyIdEnteringFirm, bytes) ← decodeUInt 1 bytes
  let (massActionReason, bytes) ← decodeUInt 1 bytes
  let (execInst, bytes) ← decodeUInt 1 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (pad6, bytes) ← Alpha.decode 6 bytes
  let (notAffectedOrdersGrpComp_, bytes) ← decodeMany NotAffectedOrdersGrpComp.decode noNotAffectedOrders.toNat bytes
  let (affectedOrdGrpComp_, bytes) ← decodeMany AffectedOrdGrpComp.decode noAffectedOrders.toNat bytes
  let (affectedOrderRequestsGrpComp_, bytes) ← decodeMany AffectedOrderRequestsGrpComp.decode noAffectedOrderRequests.toNat bytes
  if fits_notAffectedOrdersGrpComp : notAffectedOrdersGrpComp_.length < 256 ^ 2 then
    if fits_affectedOrdGrpComp : affectedOrdGrpComp_.length < 256 ^ 2 then
      if fits_affectedOrderRequestsGrpComp : affectedOrderRequestsGrpComp_.length < 256 ^ 2 then
        pure ({ pad2, rbcHeaderMeComp, massActionReportId, securityId, price, marketSegmentId, targetPartyIdSessionId, targetPartyIdExecutingTrader, partyIdEnteringTrader, partyIdEnteringFirm, massActionReason, execInst, side, pad6, notAffectedOrdersGrpComp := ⟨notAffectedOrdersGrpComp_, fits_notAffectedOrdersGrpComp⟩, affectedOrdGrpComp := ⟨affectedOrdGrpComp_, fits_affectedOrdGrpComp⟩, affectedOrderRequestsGrpComp := ⟨affectedOrderRequestsGrpComp_, fits_affectedOrderRequestsGrpComp⟩ }, bytes)
      else none
    else none
  else none

theorem encode_length_pos (message : DeleteAllOrderBroadcast) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : DeleteAllOrderBroadcast) : (encode message).length ≤ 2621514 := by
  have bound_notAffectedOrdersGrpComp := message.notAffectedOrdersGrpComp.length_lt
  have bound_affectedOrdGrpComp := message.affectedOrdGrpComp.length_lt
  have bound_affectedOrderRequestsGrpComp := message.affectedOrderRequestsGrpComp.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, RbcHeaderMeComp.encode_length, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const NotAffectedOrdersGrpComp.encode 16 NotAffectedOrdersGrpComp.encode_length, encodeMany_length_const AffectedOrdGrpComp.encode 16 AffectedOrdGrpComp.encode_length, encodeMany_length_const AffectedOrderRequestsGrpComp.encode 8 AffectedOrderRequestsGrpComp.encode_length]
  omega

@[simp] theorem decode_encode (message : DeleteAllOrderBroadcast) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RbcHeaderMeComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
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
  rw [List.append_assoc, decodeMany_bounded 2 NotAffectedOrdersGrpComp.encode NotAffectedOrdersGrpComp.decode NotAffectedOrdersGrpComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeMany_bounded 2 AffectedOrdGrpComp.encode AffectedOrdGrpComp.decode AffectedOrdGrpComp.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 AffectedOrderRequestsGrpComp.encode AffectedOrderRequestsGrpComp.decode AffectedOrderRequestsGrpComp.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.notAffectedOrdersGrpComp.length_lt, dite_eq_left message.affectedOrdGrpComp.length_lt, dite_eq_left message.affectedOrderRequestsGrpComp.length_lt]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : DeleteAllOrderBroadcast) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

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
    ++ (NrResponseHeaderMeComp.encode message.nrResponseHeaderMeComp
    ++ (encodeUIntLE 8 message.massActionReportId))

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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NrResponseHeaderMeComp.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : DeleteAllOrderNrResponse) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

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
    ++ (RbcHeaderMeComp.encode message.rbcHeaderMeComp
    ++ (encodeUIntLE 8 message.massActionReportId
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUInt 1 message.massActionReason
    ++ (encodeUInt 1 message.execInst
    ++ (Alpha.encode message.pad2v2)))))))

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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RbcHeaderMeComp.decode_encode, some_bind]
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

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : DeleteAllOrderQuoteEventBroadcast) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

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
    ++ (encodeUIntLE 8 message.trdRegTsTimeIn
    ++ (encodeUIntLE 8 message.trdRegTsTimeOut
    ++ (encodeUIntLE 8 message.responseIn
    ++ (encodeUIntLE 8 message.sendingTime
    ++ (encodeUIntLE 4 message.msgSeqNum
    ++ (encodeUIntLE 2 message.partitionId
    ++ (encodeUInt 1 message.applId
    ++ (Alpha.encode message.applMsgId
    ++ (encodeUInt 1 message.lastFragment)))))))))

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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end ResponseHeaderMeComp

/-- Delete All Order Response -/
structure DeleteAllOrderResponse where
  pad2 : Alpha 2
  responseHeaderMeComp : ResponseHeaderMeComp
  massActionReportId : BitVec 64
  pad2v2 : Alpha 2
  notAffectedOrdersGrpComp : Bounded 2 NotAffectedOrdersGrpComp
  affectedOrdGrpComp : Bounded 2 AffectedOrdGrpComp
  affectedOrderRequestsGrpComp : Bounded 2 AffectedOrderRequestsGrpComp
  deriving DecidableEq, Repr

namespace DeleteAllOrderResponse

def encode (message : DeleteAllOrderResponse) : List UInt8 :=
  Alpha.encode message.pad2
    ++ (ResponseHeaderMeComp.encode message.responseHeaderMeComp
    ++ (encodeUIntLE 8 message.massActionReportId
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.notAffectedOrdersGrpComp.val.length)
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.affectedOrdGrpComp.val.length)
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.affectedOrderRequestsGrpComp.val.length)
    ++ (Alpha.encode message.pad2v2
    ++ (encodeMany NotAffectedOrdersGrpComp.encode message.notAffectedOrdersGrpComp.val
    ++ (encodeMany AffectedOrdGrpComp.encode message.affectedOrdGrpComp.val
    ++ (encodeMany AffectedOrderRequestsGrpComp.encode message.affectedOrderRequestsGrpComp.val)))))))))

def decode (bytes : List UInt8) : Option (DeleteAllOrderResponse × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (responseHeaderMeComp, bytes) ← ResponseHeaderMeComp.decode bytes
  let (massActionReportId, bytes) ← decodeUIntLE 8 bytes
  let (noNotAffectedOrders, bytes) ← decodeUIntLE 2 bytes
  let (noAffectedOrders, bytes) ← decodeUIntLE 2 bytes
  let (noAffectedOrderRequests, bytes) ← decodeUIntLE 2 bytes
  let (pad2v2, bytes) ← Alpha.decode 2 bytes
  let (notAffectedOrdersGrpComp_, bytes) ← decodeMany NotAffectedOrdersGrpComp.decode noNotAffectedOrders.toNat bytes
  let (affectedOrdGrpComp_, bytes) ← decodeMany AffectedOrdGrpComp.decode noAffectedOrders.toNat bytes
  let (affectedOrderRequestsGrpComp_, bytes) ← decodeMany AffectedOrderRequestsGrpComp.decode noAffectedOrderRequests.toNat bytes
  if fits_notAffectedOrdersGrpComp : notAffectedOrdersGrpComp_.length < 256 ^ 2 then
    if fits_affectedOrdGrpComp : affectedOrdGrpComp_.length < 256 ^ 2 then
      if fits_affectedOrderRequestsGrpComp : affectedOrderRequestsGrpComp_.length < 256 ^ 2 then
        pure ({ pad2, responseHeaderMeComp, massActionReportId, pad2v2, notAffectedOrdersGrpComp := ⟨notAffectedOrdersGrpComp_, fits_notAffectedOrdersGrpComp⟩, affectedOrdGrpComp := ⟨affectedOrdGrpComp_, fits_affectedOrdGrpComp⟩, affectedOrderRequestsGrpComp := ⟨affectedOrderRequestsGrpComp_, fits_affectedOrderRequestsGrpComp⟩ }, bytes)
      else none
    else none
  else none

theorem encode_length_pos (message : DeleteAllOrderResponse) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : DeleteAllOrderResponse) : (encode message).length ≤ 2621482 := by
  have bound_notAffectedOrdersGrpComp := message.notAffectedOrdersGrpComp.length_lt
  have bound_affectedOrdGrpComp := message.affectedOrdGrpComp.length_lt
  have bound_affectedOrderRequestsGrpComp := message.affectedOrderRequestsGrpComp.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, ResponseHeaderMeComp.encode_length, encodeUIntLE_length, encodeMany_length_const NotAffectedOrdersGrpComp.encode 16 NotAffectedOrdersGrpComp.encode_length, encodeMany_length_const AffectedOrdGrpComp.encode 16 AffectedOrdGrpComp.encode_length, encodeMany_length_const AffectedOrderRequestsGrpComp.encode 8 AffectedOrderRequestsGrpComp.encode_length]
  omega

@[simp] theorem decode_encode (message : DeleteAllOrderResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ResponseHeaderMeComp.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeMany_bounded 2 NotAffectedOrdersGrpComp.encode NotAffectedOrdersGrpComp.decode NotAffectedOrdersGrpComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeMany_bounded 2 AffectedOrdGrpComp.encode AffectedOrdGrpComp.decode AffectedOrdGrpComp.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 AffectedOrderRequestsGrpComp.encode AffectedOrderRequestsGrpComp.decode AffectedOrderRequestsGrpComp.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.notAffectedOrdersGrpComp.length_lt, dite_eq_left message.affectedOrdGrpComp.length_lt, dite_eq_left message.affectedOrderRequestsGrpComp.length_lt]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : DeleteAllOrderResponse) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

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
  rw [decodeUIntLE_encodeUIntLE, some_bind]
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
    ++ (RbcHeaderMeComp.encode message.rbcHeaderMeComp
    ++ (encodeUIntLE 8 message.massActionReportId
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.targetPartyIdSessionId
    ++ (encodeUIntLE 4 message.partyIdEnteringTrader
    ++ (encodeUIntLE 4 message.targetPartyIdExecutingTrader
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.notAffectedSecuritiesGrpComp.val.length)
    ++ (encodeUInt 1 message.massActionReason
    ++ (encodeUInt 1 message.partyIdEnteringFirm
    ++ (Alpha.encode message.targetPartyIdDeskId
    ++ (Alpha.encode message.pad1
    ++ (encodeMany NotAffectedSecuritiesGrpComp.encode message.notAffectedSecuritiesGrpComp.val)))))))))))))

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
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : DeleteAllQuoteBroadcast) : (encode message).length ≤ 524378 := by
  have bound_notAffectedSecuritiesGrpComp := message.notAffectedSecuritiesGrpComp.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, RbcHeaderMeComp.encode_length, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const NotAffectedSecuritiesGrpComp.encode 8 NotAffectedSecuritiesGrpComp.encode_length]
  omega

@[simp] theorem decode_encode (message : DeleteAllQuoteBroadcast) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RbcHeaderMeComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
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
  rw [decodeMany_bounded 2 NotAffectedSecuritiesGrpComp.encode NotAffectedSecuritiesGrpComp.decode NotAffectedSecuritiesGrpComp.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.notAffectedSecuritiesGrpComp.length_lt]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : DeleteAllQuoteBroadcast) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

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
    ++ (NrResponseHeaderMeComp.encode message.nrResponseHeaderMeComp
    ++ (encodeUIntLE 8 message.massActionReportId
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.notAffectedSecuritiesGrpComp.val.length)
    ++ (Alpha.encode message.pad6
    ++ (encodeMany NotAffectedSecuritiesGrpComp.encode message.notAffectedSecuritiesGrpComp.val)))))

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
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : DeleteAllQuoteResponse) : (encode message).length ≤ 524346 := by
  have bound_notAffectedSecuritiesGrpComp := message.notAffectedSecuritiesGrpComp.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, NrResponseHeaderMeComp.encode_length, encodeUIntLE_length, encodeMany_length_const NotAffectedSecuritiesGrpComp.encode 8 NotAffectedSecuritiesGrpComp.encode_length]
  omega

@[simp] theorem decode_encode (message : DeleteAllQuoteResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NrResponseHeaderMeComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 NotAffectedSecuritiesGrpComp.encode NotAffectedSecuritiesGrpComp.decode NotAffectedSecuritiesGrpComp.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.notAffectedSecuritiesGrpComp.length_lt]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : DeleteAllQuoteResponse) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end DeleteAllQuoteResponse

/-- Delete Order Broadcast: 178 bytes -/
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
  quoteId : BitVec 64
  orderIdSfx : BitVec 32
  marketSegmentId : BitVec 32
  partyIdEnteringTrader : BitVec 32
  partyIdSessionId : BitVec 32
  execRestatementReason : BitVec 16
  partyIdEnteringFirm : BitVec 8
  ordStatus : OrdStatus
  execType : ExecType
  side : BitVec 8
  orderEventType : BitVec 8
  fixClOrdId : Alpha 20
  partyEnteringFirm : Alpha 5
  partyEnteringTrader : Alpha 6
  pad2v2 : Alpha 2
  deriving DecidableEq, Repr

namespace DeleteOrderBroadcast

def encode (message : DeleteOrderBroadcast) : List UInt8 :=
  Alpha.encode message.pad2
    ++ (RbcHeaderMeComp.encode message.rbcHeaderMeComp
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 8 message.origClOrdId
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.execId
    ++ (encodeUIntLE 8 message.cumQty
    ++ (encodeUIntLE 8 message.cxlQty
    ++ (encodeUIntLE 8 message.quoteId
    ++ (encodeUIntLE 4 message.orderIdSfx
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.partyIdEnteringTrader
    ++ (encodeUIntLE 4 message.partyIdSessionId
    ++ (encodeUIntLE 2 message.execRestatementReason
    ++ (encodeUInt 1 message.partyIdEnteringFirm
    ++ (OrdStatus.encode message.ordStatus
    ++ (ExecType.encode message.execType
    ++ (encodeUInt 1 message.side
    ++ (encodeUInt 1 message.orderEventType
    ++ (Alpha.encode message.fixClOrdId
    ++ (Alpha.encode message.partyEnteringFirm
    ++ (Alpha.encode message.partyEnteringTrader
    ++ (Alpha.encode message.pad2v2)))))))))))))))))))))))

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
  let (quoteId, bytes) ← decodeUIntLE 8 bytes
  let (orderIdSfx, bytes) ← decodeUIntLE 4 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (partyIdEnteringTrader, bytes) ← decodeUIntLE 4 bytes
  let (partyIdSessionId, bytes) ← decodeUIntLE 4 bytes
  let (execRestatementReason, bytes) ← decodeUIntLE 2 bytes
  let (partyIdEnteringFirm, bytes) ← decodeUInt 1 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (orderEventType, bytes) ← decodeUInt 1 bytes
  let (fixClOrdId, bytes) ← Alpha.decode 20 bytes
  let (partyEnteringFirm, bytes) ← Alpha.decode 5 bytes
  let (partyEnteringTrader, bytes) ← Alpha.decode 6 bytes
  let (pad2v2, bytes) ← Alpha.decode 2 bytes
  pure ({ pad2, rbcHeaderMeComp, orderId, clOrdId, origClOrdId, securityId, execId, cumQty, cxlQty, quoteId, orderIdSfx, marketSegmentId, partyIdEnteringTrader, partyIdSessionId, execRestatementReason, partyIdEnteringFirm, ordStatus, execType, side, orderEventType, fixClOrdId, partyEnteringFirm, partyEnteringTrader, pad2v2 }, bytes)

@[simp] theorem encode_length (message : DeleteOrderBroadcast) : (encode message).length = 178 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RbcHeaderMeComp.encode_length, encodeUIntLE_length, encodeUInt_length, OrdStatus.encode_length, ExecType.encode_length]

theorem encode_length_pos (message : DeleteOrderBroadcast) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DeleteOrderBroadcast) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RbcHeaderMeComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
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
  rw [List.append_assoc, OrdStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExecType.decode_encode, some_bind]
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

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : DeleteOrderBroadcast) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end DeleteOrderBroadcast

/-- Delete Order Nr Response: 122 bytes -/
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
  orderIdSfx : BitVec 32
  ordStatus : OrdStatus
  execType : ExecType
  execRestatementReason : BitVec 16
  transactionDelayIndicator : BitVec 8
  pad7 : Alpha 7
  deriving DecidableEq, Repr

namespace DeleteOrderNrResponse

def encode (message : DeleteOrderNrResponse) : List UInt8 :=
  Alpha.encode message.pad2
    ++ (NrResponseHeaderMeComp.encode message.nrResponseHeaderMeComp
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 8 message.origClOrdId
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.execId
    ++ (encodeUIntLE 8 message.cumQty
    ++ (encodeUIntLE 8 message.cxlQty
    ++ (encodeUIntLE 4 message.orderIdSfx
    ++ (OrdStatus.encode message.ordStatus
    ++ (ExecType.encode message.execType
    ++ (encodeUIntLE 2 message.execRestatementReason
    ++ (encodeUInt 1 message.transactionDelayIndicator
    ++ (Alpha.encode message.pad7))))))))))))))

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
  let (orderIdSfx, bytes) ← decodeUIntLE 4 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (execRestatementReason, bytes) ← decodeUIntLE 2 bytes
  let (transactionDelayIndicator, bytes) ← decodeUInt 1 bytes
  let (pad7, bytes) ← Alpha.decode 7 bytes
  pure ({ pad2, nrResponseHeaderMeComp, orderId, clOrdId, origClOrdId, securityId, execId, cumQty, cxlQty, orderIdSfx, ordStatus, execType, execRestatementReason, transactionDelayIndicator, pad7 }, bytes)

@[simp] theorem encode_length (message : DeleteOrderNrResponse) : (encode message).length = 122 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, NrResponseHeaderMeComp.encode_length, encodeUIntLE_length, OrdStatus.encode_length, ExecType.encode_length, encodeUInt_length]

theorem encode_length_pos (message : DeleteOrderNrResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DeleteOrderNrResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NrResponseHeaderMeComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, OrdStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExecType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : DeleteOrderNrResponse) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end DeleteOrderNrResponse

/-- Delete Order Response: 138 bytes -/
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
  orderIdSfx : BitVec 32
  ordStatus : OrdStatus
  execType : ExecType
  execRestatementReason : BitVec 16
  transactionDelayIndicator : BitVec 8
  pad7 : Alpha 7
  deriving DecidableEq, Repr

namespace DeleteOrderResponse

def encode (message : DeleteOrderResponse) : List UInt8 :=
  Alpha.encode message.pad2
    ++ (ResponseHeaderMeComp.encode message.responseHeaderMeComp
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 8 message.origClOrdId
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.execId
    ++ (encodeUIntLE 8 message.cumQty
    ++ (encodeUIntLE 8 message.cxlQty
    ++ (encodeUIntLE 4 message.orderIdSfx
    ++ (OrdStatus.encode message.ordStatus
    ++ (ExecType.encode message.execType
    ++ (encodeUIntLE 2 message.execRestatementReason
    ++ (encodeUInt 1 message.transactionDelayIndicator
    ++ (Alpha.encode message.pad7))))))))))))))

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
  let (orderIdSfx, bytes) ← decodeUIntLE 4 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (execRestatementReason, bytes) ← decodeUIntLE 2 bytes
  let (transactionDelayIndicator, bytes) ← decodeUInt 1 bytes
  let (pad7, bytes) ← Alpha.decode 7 bytes
  pure ({ pad2, responseHeaderMeComp, orderId, clOrdId, origClOrdId, securityId, execId, cumQty, cxlQty, orderIdSfx, ordStatus, execType, execRestatementReason, transactionDelayIndicator, pad7 }, bytes)

@[simp] theorem encode_length (message : DeleteOrderResponse) : (encode message).length = 138 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, ResponseHeaderMeComp.encode_length, encodeUIntLE_length, OrdStatus.encode_length, ExecType.encode_length, encodeUInt_length]

theorem encode_length_pos (message : DeleteOrderResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DeleteOrderResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ResponseHeaderMeComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, OrdStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExecType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : DeleteOrderResponse) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end DeleteOrderResponse

/-- Extended Deletion Report: 338 bytes -/
structure ExtendedDeletionReport where
  pad2 : Alpha 2
  rbcHeaderMeComp : RbcHeaderMeComp
  orderId : BitVec 64
  clOrdId : BitVec 64
  origClOrdId : BitVec 64
  securityId : BitVec 64
  execId : BitVec 64
  trdRegTsEntryTime : BitVec 64
  price : BitVec 64
  leavesQty : BitVec 64
  cumQty : BitVec 64
  cxlQty : BitVec 64
  orderQty : BitVec 64
  displayQty : BitVec 64
  displayLowQty : BitVec 64
  displayHighQty : BitVec 64
  stopPx : BitVec 64
  volumeDiscoveryPrice : BitVec 64
  pegOffsetValueAbs : BitVec 64
  pegOffsetValuePct : BitVec 64
  quoteId : BitVec 64
  marketSegmentId : BitVec 32
  orderIdSfx : BitVec 32
  expireDate : BitVec 32
  matchInstCrossId : BitVec 32
  partyIdExecutingUnit : BitVec 32
  partyIdSessionId : BitVec 32
  partyIdExecutingTrader : BitVec 32
  partyIdEnteringTrader : BitVec 32
  execRestatementReason : BitVec 16
  ordStatus : OrdStatus
  execType : ExecType
  side : BitVec 8
  ordType : BitVec 8
  tradingCapacity : BitVec 8
  timeInForce : BitVec 8
  execInst : BitVec 8
  tradingSessionSubId : BitVec 8
  applSeqIndicator : BitVec 8
  exDestinationType : BitVec 8
  freeText1 : Alpha 12
  freeText2 : Alpha 12
  freeText4 : Alpha 16
  partyEnteringFirm : Alpha 5
  partyEnteringTrader : Alpha 6
  partyExecutingFirm : Alpha 5
  partyExecutingTrader : Alpha 6
  fixClOrdId : Alpha 20
  triggered : BitVec 8
  pad1 : Alpha 1
  deriving DecidableEq, Repr

namespace ExtendedDeletionReport

def encode (message : ExtendedDeletionReport) : List UInt8 :=
  Alpha.encode message.pad2
    ++ (RbcHeaderMeComp.encode message.rbcHeaderMeComp
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 8 message.origClOrdId
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.execId
    ++ (encodeUIntLE 8 message.trdRegTsEntryTime
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 8 message.leavesQty
    ++ (encodeUIntLE 8 message.cumQty
    ++ (encodeUIntLE 8 message.cxlQty
    ++ (encodeUIntLE 8 message.orderQty
    ++ (encodeUIntLE 8 message.displayQty
    ++ (encodeUIntLE 8 message.displayLowQty
    ++ (encodeUIntLE 8 message.displayHighQty
    ++ (encodeUIntLE 8 message.stopPx
    ++ (encodeUIntLE 8 message.volumeDiscoveryPrice
    ++ (encodeUIntLE 8 message.pegOffsetValueAbs
    ++ (encodeUIntLE 8 message.pegOffsetValuePct
    ++ (encodeUIntLE 8 message.quoteId
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.orderIdSfx
    ++ (encodeUIntLE 4 message.expireDate
    ++ (encodeUIntLE 4 message.matchInstCrossId
    ++ (encodeUIntLE 4 message.partyIdExecutingUnit
    ++ (encodeUIntLE 4 message.partyIdSessionId
    ++ (encodeUIntLE 4 message.partyIdExecutingTrader
    ++ (encodeUIntLE 4 message.partyIdEnteringTrader
    ++ (encodeUIntLE 2 message.execRestatementReason
    ++ (OrdStatus.encode message.ordStatus
    ++ (ExecType.encode message.execType
    ++ (encodeUInt 1 message.side
    ++ (encodeUInt 1 message.ordType
    ++ (encodeUInt 1 message.tradingCapacity
    ++ (encodeUInt 1 message.timeInForce
    ++ (encodeUInt 1 message.execInst
    ++ (encodeUInt 1 message.tradingSessionSubId
    ++ (encodeUInt 1 message.applSeqIndicator
    ++ (encodeUInt 1 message.exDestinationType
    ++ (Alpha.encode message.freeText1
    ++ (Alpha.encode message.freeText2
    ++ (Alpha.encode message.freeText4
    ++ (Alpha.encode message.partyEnteringFirm
    ++ (Alpha.encode message.partyEnteringTrader
    ++ (Alpha.encode message.partyExecutingFirm
    ++ (Alpha.encode message.partyExecutingTrader
    ++ (Alpha.encode message.fixClOrdId
    ++ (encodeUInt 1 message.triggered
    ++ (Alpha.encode message.pad1)))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (ExtendedDeletionReport × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderMeComp, bytes) ← RbcHeaderMeComp.decode bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (origClOrdId, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  let (trdRegTsEntryTime, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (leavesQty, bytes) ← decodeUIntLE 8 bytes
  let (cumQty, bytes) ← decodeUIntLE 8 bytes
  let (cxlQty, bytes) ← decodeUIntLE 8 bytes
  let (orderQty, bytes) ← decodeUIntLE 8 bytes
  let (displayQty, bytes) ← decodeUIntLE 8 bytes
  let (displayLowQty, bytes) ← decodeUIntLE 8 bytes
  let (displayHighQty, bytes) ← decodeUIntLE 8 bytes
  let (stopPx, bytes) ← decodeUIntLE 8 bytes
  let (volumeDiscoveryPrice, bytes) ← decodeUIntLE 8 bytes
  let (pegOffsetValueAbs, bytes) ← decodeUIntLE 8 bytes
  let (pegOffsetValuePct, bytes) ← decodeUIntLE 8 bytes
  let (quoteId, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (orderIdSfx, bytes) ← decodeUIntLE 4 bytes
  let (expireDate, bytes) ← decodeUIntLE 4 bytes
  let (matchInstCrossId, bytes) ← decodeUIntLE 4 bytes
  let (partyIdExecutingUnit, bytes) ← decodeUIntLE 4 bytes
  let (partyIdSessionId, bytes) ← decodeUIntLE 4 bytes
  let (partyIdExecutingTrader, bytes) ← decodeUIntLE 4 bytes
  let (partyIdEnteringTrader, bytes) ← decodeUIntLE 4 bytes
  let (execRestatementReason, bytes) ← decodeUIntLE 2 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (ordType, bytes) ← decodeUInt 1 bytes
  let (tradingCapacity, bytes) ← decodeUInt 1 bytes
  let (timeInForce, bytes) ← decodeUInt 1 bytes
  let (execInst, bytes) ← decodeUInt 1 bytes
  let (tradingSessionSubId, bytes) ← decodeUInt 1 bytes
  let (applSeqIndicator, bytes) ← decodeUInt 1 bytes
  let (exDestinationType, bytes) ← decodeUInt 1 bytes
  let (freeText1, bytes) ← Alpha.decode 12 bytes
  let (freeText2, bytes) ← Alpha.decode 12 bytes
  let (freeText4, bytes) ← Alpha.decode 16 bytes
  let (partyEnteringFirm, bytes) ← Alpha.decode 5 bytes
  let (partyEnteringTrader, bytes) ← Alpha.decode 6 bytes
  let (partyExecutingFirm, bytes) ← Alpha.decode 5 bytes
  let (partyExecutingTrader, bytes) ← Alpha.decode 6 bytes
  let (fixClOrdId, bytes) ← Alpha.decode 20 bytes
  let (triggered, bytes) ← decodeUInt 1 bytes
  let (pad1, bytes) ← Alpha.decode 1 bytes
  pure ({ pad2, rbcHeaderMeComp, orderId, clOrdId, origClOrdId, securityId, execId, trdRegTsEntryTime, price, leavesQty, cumQty, cxlQty, orderQty, displayQty, displayLowQty, displayHighQty, stopPx, volumeDiscoveryPrice, pegOffsetValueAbs, pegOffsetValuePct, quoteId, marketSegmentId, orderIdSfx, expireDate, matchInstCrossId, partyIdExecutingUnit, partyIdSessionId, partyIdExecutingTrader, partyIdEnteringTrader, execRestatementReason, ordStatus, execType, side, ordType, tradingCapacity, timeInForce, execInst, tradingSessionSubId, applSeqIndicator, exDestinationType, freeText1, freeText2, freeText4, partyEnteringFirm, partyEnteringTrader, partyExecutingFirm, partyExecutingTrader, fixClOrdId, triggered, pad1 }, bytes)

@[simp] theorem encode_length (message : ExtendedDeletionReport) : (encode message).length = 338 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RbcHeaderMeComp.encode_length, encodeUIntLE_length, OrdStatus.encode_length, ExecType.encode_length, encodeUInt_length]

theorem encode_length_pos (message : ExtendedDeletionReport) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : ExtendedDeletionReport) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RbcHeaderMeComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, OrdStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExecType.decode_encode, some_bind]
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
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : ExtendedDeletionReport) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end ExtendedDeletionReport

/-- Forced Logout Notification -/
structure ForcedLogoutNotification where
  pad2 : Alpha 2
  notifHeaderComp : NotifHeaderComp
  pad6 : Alpha 6
  varText : Bounded 2 UInt8
  alignmentPadding : Capped 7
  deriving DecidableEq, Repr

namespace ForcedLogoutNotification

def encode (message : ForcedLogoutNotification) : List UInt8 :=
  Alpha.encode message.pad2
    ++ (NotifHeaderComp.encode message.notifHeaderComp
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.varText.val.length)
    ++ (Alpha.encode message.pad6
    ++ (encodeMany Byte.encode message.varText.val
    ++ (message.alignmentPadding.val)))))

def decode (bytes : List UInt8) : Option ForcedLogoutNotification := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (notifHeaderComp, bytes) ← NotifHeaderComp.decode bytes
  let (varTextLen, bytes) ← decodeUIntLE 2 bytes
  let (pad6, bytes) ← Alpha.decode 6 bytes
  let (varText_, bytes) ← decodeMany Byte.decode varTextLen.toNat bytes
  let alignmentPadding_ := bytes
  if fits_varText : varText_.length < 256 ^ 2 then
    if fits_alignmentPadding : alignmentPadding_.length ≤ 7 then
      pure { pad2, notifHeaderComp, pad6, varText := ⟨varText_, fits_varText⟩, alignmentPadding := ⟨alignmentPadding_, fits_alignmentPadding⟩ }
    else none
  else none

theorem encode_length_pos (message : ForcedLogoutNotification) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ForcedLogoutNotification) : (encode message).length ≤ 65560 := by
  have bound_varText := message.varText.length_lt
  have bound_alignmentPadding := message.alignmentPadding.length_le
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, NotifHeaderComp.encode_length, encodeUIntLE_length, encodeMany_length_const Byte.encode 1 Byte.encode_length]
  omega

theorem decode_encode (message : ForcedLogoutNotification) : decode (encode message) = some message := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  dsimp only
  rw [NotifHeaderComp.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 Byte.encode Byte.decode Byte.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.varText.length_lt, dite_eq_left message.alignmentPadding.length_le]
  rfl

end ForcedLogoutNotification

/-- Forced User Logout Notification -/
structure ForcedUserLogoutNotification where
  pad2 : Alpha 2
  notifHeaderComp : NotifHeaderComp
  userStatus : BitVec 8
  pad3 : Alpha 3
  username : BitVec 32
  pad6 : Alpha 6
  varText : Bounded 2 UInt8
  alignmentPadding : Capped 7
  deriving DecidableEq, Repr

namespace ForcedUserLogoutNotification

def encode (message : ForcedUserLogoutNotification) : List UInt8 :=
  Alpha.encode message.pad2
    ++ (NotifHeaderComp.encode message.notifHeaderComp
    ++ (encodeUInt 1 message.userStatus
    ++ (Alpha.encode message.pad3
    ++ (encodeUIntLE 4 message.username
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.varText.val.length)
    ++ (Alpha.encode message.pad6
    ++ (encodeMany Byte.encode message.varText.val
    ++ (message.alignmentPadding.val))))))))

def decode (bytes : List UInt8) : Option ForcedUserLogoutNotification := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (notifHeaderComp, bytes) ← NotifHeaderComp.decode bytes
  let (userStatus, bytes) ← decodeUInt 1 bytes
  let (pad3, bytes) ← Alpha.decode 3 bytes
  let (username, bytes) ← decodeUIntLE 4 bytes
  let (varTextLen, bytes) ← decodeUIntLE 2 bytes
  let (pad6, bytes) ← Alpha.decode 6 bytes
  let (varText_, bytes) ← decodeMany Byte.decode varTextLen.toNat bytes
  let alignmentPadding_ := bytes
  if fits_varText : varText_.length < 256 ^ 2 then
    if fits_alignmentPadding : alignmentPadding_.length ≤ 7 then
      pure { pad2, notifHeaderComp, userStatus, pad3, username, pad6, varText := ⟨varText_, fits_varText⟩, alignmentPadding := ⟨alignmentPadding_, fits_alignmentPadding⟩ }
    else none
  else none

theorem encode_length_pos (message : ForcedUserLogoutNotification) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ForcedUserLogoutNotification) : (encode message).length ≤ 65568 := by
  have bound_varText := message.varText.length_lt
  have bound_alignmentPadding := message.alignmentPadding.length_le
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, NotifHeaderComp.encode_length, encodeUInt_length, encodeUIntLE_length, encodeMany_length_const Byte.encode 1 Byte.encode_length]
  omega

theorem decode_encode (message : ForcedUserLogoutNotification) : decode (encode message) = some message := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  dsimp only
  rw [NotifHeaderComp.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 Byte.encode Byte.decode Byte.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.varText.length_lt, dite_eq_left message.alignmentPadding.length_le]
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
    ++ (NotifHeaderComp.encode message.notifHeaderComp)

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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [NotifHeaderComp.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : HeartbeatNotification) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end HeartbeatNotification

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
    ++ (encodeUIntLE 8 message.sendingTime
    ++ (encodeUIntLE 4 message.msgSeqNum
    ++ (Alpha.encode message.pad4)))

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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ResponseHeaderComp

/-- Enrichment Rules Grp Comp: 48 bytes -/
structure EnrichmentRulesGrpComp where
  enrichmentRuleId : BitVec 16
  freeText1 : Alpha 12
  freeText2 : Alpha 12
  freeText4 : Alpha 16
  pad6 : Alpha 6
  deriving DecidableEq, Repr

namespace EnrichmentRulesGrpComp

def encode (message : EnrichmentRulesGrpComp) : List UInt8 :=
  encodeUIntLE 2 message.enrichmentRuleId
    ++ (Alpha.encode message.freeText1
    ++ (Alpha.encode message.freeText2
    ++ (Alpha.encode message.freeText4
    ++ (Alpha.encode message.pad6))))

def decode (bytes : List UInt8) : Option (EnrichmentRulesGrpComp × List UInt8) := do
  let (enrichmentRuleId, bytes) ← decodeUIntLE 2 bytes
  let (freeText1, bytes) ← Alpha.decode 12 bytes
  let (freeText2, bytes) ← Alpha.decode 12 bytes
  let (freeText4, bytes) ← Alpha.decode 16 bytes
  let (pad6, bytes) ← Alpha.decode 6 bytes
  pure ({ enrichmentRuleId, freeText1, freeText2, freeText4, pad6 }, bytes)

@[simp] theorem encode_length (message : EnrichmentRulesGrpComp) : (encode message).length = 48 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length]

theorem encode_length_pos (message : EnrichmentRulesGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EnrichmentRulesGrpComp) (rest : List UInt8) :
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
    ++ (ResponseHeaderComp.encode message.responseHeaderComp
    ++ (Alpha.encode message.lastEntityProcessed
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.enrichmentRulesGrpComp.val.length)
    ++ (Alpha.encode message.pad6
    ++ (encodeMany EnrichmentRulesGrpComp.encode message.enrichmentRulesGrpComp.val)))))

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
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : InquireEnrichmentRuleIdListResponse) : (encode message).length ≤ 3145730 := by
  have bound_enrichmentRulesGrpComp := message.enrichmentRulesGrpComp.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, ResponseHeaderComp.encode_length, encodeUIntLE_length, encodeMany_length_const EnrichmentRulesGrpComp.encode 48 EnrichmentRulesGrpComp.encode_length]
  omega

@[simp] theorem decode_encode (message : InquireEnrichmentRuleIdListResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ResponseHeaderComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 EnrichmentRulesGrpComp.encode EnrichmentRulesGrpComp.decode EnrichmentRulesGrpComp.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.enrichmentRulesGrpComp.length_lt]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : InquireEnrichmentRuleIdListResponse) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end InquireEnrichmentRuleIdListResponse

/-- Sessions Grp Comp: 8 bytes -/
structure SessionsGrpComp where
  partyIdSessionId : BitVec 32
  sessionMode : BitVec 8
  sessionSubMode : BitVec 8
  pad2 : Alpha 2
  deriving DecidableEq, Repr

namespace SessionsGrpComp

def encode (message : SessionsGrpComp) : List UInt8 :=
  encodeUIntLE 4 message.partyIdSessionId
    ++ (encodeUInt 1 message.sessionMode
    ++ (encodeUInt 1 message.sessionSubMode
    ++ (Alpha.encode message.pad2)))

def decode (bytes : List UInt8) : Option (SessionsGrpComp × List UInt8) := do
  let (partyIdSessionId, bytes) ← decodeUIntLE 4 bytes
  let (sessionMode, bytes) ← decodeUInt 1 bytes
  let (sessionSubMode, bytes) ← decodeUInt 1 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  pure ({ partyIdSessionId, sessionMode, sessionSubMode, pad2 }, bytes)

@[simp] theorem encode_length (message : SessionsGrpComp) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : SessionsGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SessionsGrpComp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
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
    ++ (ResponseHeaderComp.encode message.responseHeaderComp
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.sessionsGrpComp.val.length)
    ++ (Alpha.encode message.pad6
    ++ (encodeMany SessionsGrpComp.encode message.sessionsGrpComp.val))))

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
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : InquireSessionListResponse) : (encode message).length ≤ 524314 := by
  have bound_sessionsGrpComp := message.sessionsGrpComp.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, ResponseHeaderComp.encode_length, encodeUIntLE_length, encodeMany_length_const SessionsGrpComp.encode 8 SessionsGrpComp.encode_length]
  omega

@[simp] theorem decode_encode (message : InquireSessionListResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ResponseHeaderComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 SessionsGrpComp.encode SessionsGrpComp.decode SessionsGrpComp.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.sessionsGrpComp.length_lt]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : InquireSessionListResponse) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end InquireSessionListResponse

/-- Party Details Grp Comp: 16 bytes -/
structure PartyDetailsGrpComp where
  partyDetailIdExecutingTrader : BitVec 32
  partyDetailExecutingTrader : Alpha 6
  partyDetailRoleQualifier : BitVec 8
  partyDetailStatus : BitVec 8
  partyDetailDeskId : Alpha 3
  pad1 : Alpha 1
  deriving DecidableEq, Repr

namespace PartyDetailsGrpComp

def encode (message : PartyDetailsGrpComp) : List UInt8 :=
  encodeUIntLE 4 message.partyDetailIdExecutingTrader
    ++ (Alpha.encode message.partyDetailExecutingTrader
    ++ (encodeUInt 1 message.partyDetailRoleQualifier
    ++ (encodeUInt 1 message.partyDetailStatus
    ++ (Alpha.encode message.partyDetailDeskId
    ++ (Alpha.encode message.pad1)))))

def decode (bytes : List UInt8) : Option (PartyDetailsGrpComp × List UInt8) := do
  let (partyDetailIdExecutingTrader, bytes) ← decodeUIntLE 4 bytes
  let (partyDetailExecutingTrader, bytes) ← Alpha.decode 6 bytes
  let (partyDetailRoleQualifier, bytes) ← decodeUInt 1 bytes
  let (partyDetailStatus, bytes) ← decodeUInt 1 bytes
  let (partyDetailDeskId, bytes) ← Alpha.decode 3 bytes
  let (pad1, bytes) ← Alpha.decode 1 bytes
  pure ({ partyDetailIdExecutingTrader, partyDetailExecutingTrader, partyDetailRoleQualifier, partyDetailStatus, partyDetailDeskId, pad1 }, bytes)

@[simp] theorem encode_length (message : PartyDetailsGrpComp) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : PartyDetailsGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : PartyDetailsGrpComp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
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
    ++ (ResponseHeaderComp.encode message.responseHeaderComp
    ++ (Alpha.encode message.lastEntityProcessed
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.partyDetailsGrpComp.val.length)
    ++ (Alpha.encode message.pad6
    ++ (encodeMany PartyDetailsGrpComp.encode message.partyDetailsGrpComp.val)))))

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
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : InquireUserResponse) : (encode message).length ≤ 1048610 := by
  have bound_partyDetailsGrpComp := message.partyDetailsGrpComp.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, ResponseHeaderComp.encode_length, encodeUIntLE_length, encodeMany_length_const PartyDetailsGrpComp.encode 16 PartyDetailsGrpComp.encode_length]
  omega

@[simp] theorem decode_encode (message : InquireUserResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ResponseHeaderComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 PartyDetailsGrpComp.encode PartyDetailsGrpComp.decode PartyDetailsGrpComp.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.partyDetailsGrpComp.length_lt]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : InquireUserResponse) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end InquireUserResponse

/-- Issuer Notification: 122 bytes -/
structure IssuerNotification where
  pad2 : Alpha 2
  rbcHeaderMeComp : RbcHeaderMeComp
  securityId : BitVec 64
  transactTime : BitVec 64
  lastPx : BitVec 64
  potentialExecVolume : BitVec 64
  lastQty : BitVec 64
  imbalanceQty : BitVec 64
  marketSegmentId : BitVec 32
  partyIdSessionId : BitVec 32
  securityTradingStatus : BitVec 8
  pad7 : Alpha 7
  deriving DecidableEq, Repr

namespace IssuerNotification

def encode (message : IssuerNotification) : List UInt8 :=
  Alpha.encode message.pad2
    ++ (RbcHeaderMeComp.encode message.rbcHeaderMeComp
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 8 message.lastPx
    ++ (encodeUIntLE 8 message.potentialExecVolume
    ++ (encodeUIntLE 8 message.lastQty
    ++ (encodeUIntLE 8 message.imbalanceQty
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.partyIdSessionId
    ++ (encodeUInt 1 message.securityTradingStatus
    ++ (Alpha.encode message.pad7)))))))))))

def decode (bytes : List UInt8) : Option (IssuerNotification × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderMeComp, bytes) ← RbcHeaderMeComp.decode bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  let (potentialExecVolume, bytes) ← decodeUIntLE 8 bytes
  let (lastQty, bytes) ← decodeUIntLE 8 bytes
  let (imbalanceQty, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (partyIdSessionId, bytes) ← decodeUIntLE 4 bytes
  let (securityTradingStatus, bytes) ← decodeUInt 1 bytes
  let (pad7, bytes) ← Alpha.decode 7 bytes
  pure ({ pad2, rbcHeaderMeComp, securityId, transactTime, lastPx, potentialExecVolume, lastQty, imbalanceQty, marketSegmentId, partyIdSessionId, securityTradingStatus, pad7 }, bytes)

@[simp] theorem encode_length (message : IssuerNotification) : (encode message).length = 122 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RbcHeaderMeComp.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : IssuerNotification) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IssuerNotification) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RbcHeaderMeComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
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

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : IssuerNotification) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end IssuerNotification

/-- Issuer Security State Change Response: 58 bytes -/
structure IssuerSecurityStateChangeResponse where
  pad2 : Alpha 2
  nrResponseHeaderMeComp : NrResponseHeaderMeComp
  securityStatusReportId : BitVec 64
  deriving DecidableEq, Repr

namespace IssuerSecurityStateChangeResponse

def encode (message : IssuerSecurityStateChangeResponse) : List UInt8 :=
  Alpha.encode message.pad2
    ++ (NrResponseHeaderMeComp.encode message.nrResponseHeaderMeComp
    ++ (encodeUIntLE 8 message.securityStatusReportId))

def decode (bytes : List UInt8) : Option (IssuerSecurityStateChangeResponse × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (nrResponseHeaderMeComp, bytes) ← NrResponseHeaderMeComp.decode bytes
  let (securityStatusReportId, bytes) ← decodeUIntLE 8 bytes
  pure ({ pad2, nrResponseHeaderMeComp, securityStatusReportId }, bytes)

@[simp] theorem encode_length (message : IssuerSecurityStateChangeResponse) : (encode message).length = 58 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, NrResponseHeaderMeComp.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : IssuerSecurityStateChangeResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : IssuerSecurityStateChangeResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NrResponseHeaderMeComp.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : IssuerSecurityStateChangeResponse) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end IssuerSecurityStateChangeResponse

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
    ++ (encodeUIntLE 8 message.applSeqNum
    ++ (encodeUIntLE 4 message.applSubId
    ++ (encodeUIntLE 2 message.partitionId
    ++ (encodeUInt 1 message.applResendFlag
    ++ (encodeUInt 1 message.applId
    ++ (encodeUInt 1 message.lastFragment
    ++ (Alpha.encode message.pad7)))))))

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

end RbcHeaderComp

/-- Legal Notification Broadcast -/
structure LegalNotificationBroadcast where
  pad2 : Alpha 2
  rbcHeaderComp : RbcHeaderComp
  transactTime : BitVec 64
  userStatus : BitVec 8
  pad5 : Alpha 5
  varText : Bounded 2 UInt8
  alignmentPadding : Capped 7
  deriving DecidableEq, Repr

namespace LegalNotificationBroadcast

def encode (message : LegalNotificationBroadcast) : List UInt8 :=
  Alpha.encode message.pad2
    ++ (RbcHeaderComp.encode message.rbcHeaderComp
    ++ (encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.varText.val.length)
    ++ (encodeUInt 1 message.userStatus
    ++ (Alpha.encode message.pad5
    ++ (encodeMany Byte.encode message.varText.val
    ++ (message.alignmentPadding.val)))))))

def decode (bytes : List UInt8) : Option LegalNotificationBroadcast := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderComp, bytes) ← RbcHeaderComp.decode bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (varTextLen, bytes) ← decodeUIntLE 2 bytes
  let (userStatus, bytes) ← decodeUInt 1 bytes
  let (pad5, bytes) ← Alpha.decode 5 bytes
  let (varText_, bytes) ← decodeMany Byte.decode varTextLen.toNat bytes
  let alignmentPadding_ := bytes
  if fits_varText : varText_.length < 256 ^ 2 then
    if fits_alignmentPadding : alignmentPadding_.length ≤ 7 then
      pure { pad2, rbcHeaderComp, transactTime, userStatus, pad5, varText := ⟨varText_, fits_varText⟩, alignmentPadding := ⟨alignmentPadding_, fits_alignmentPadding⟩ }
    else none
  else none

theorem encode_length_pos (message : LegalNotificationBroadcast) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : LegalNotificationBroadcast) : (encode message).length ≤ 65592 := by
  have bound_varText := message.varText.length_lt
  have bound_alignmentPadding := message.alignmentPadding.length_le
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, RbcHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const Byte.encode 1 Byte.encode_length]
  omega

theorem decode_encode (message : LegalNotificationBroadcast) : decode (encode message) = some message := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  dsimp only
  rw [RbcHeaderComp.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 Byte.encode Byte.decode Byte.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.varText.length_lt, dite_eq_left message.alignmentPadding.length_le]
  rfl

end LegalNotificationBroadcast

/-- Logon Response: 90 bytes -/
structure LogonResponse where
  pad2 : Alpha 2
  responseHeaderComp : ResponseHeaderComp
  throttleTimeInterval : BitVec 64
  throttleNoMsgs : BitVec 32
  throttleDisconnectLimit : BitVec 32
  heartBtInt : BitVec 32
  sessionInstanceId : BitVec 32
  marketId : BitVec 16
  tradSesMode : BitVec 8
  defaultCstmApplVerId : Alpha 30
  defaultCstmApplVerSubId : Alpha 5
  pad2v2 : Alpha 2
  deriving DecidableEq, Repr

namespace LogonResponse

def encode (message : LogonResponse) : List UInt8 :=
  Alpha.encode message.pad2
    ++ (ResponseHeaderComp.encode message.responseHeaderComp
    ++ (encodeUIntLE 8 message.throttleTimeInterval
    ++ (encodeUIntLE 4 message.throttleNoMsgs
    ++ (encodeUIntLE 4 message.throttleDisconnectLimit
    ++ (encodeUIntLE 4 message.heartBtInt
    ++ (encodeUIntLE 4 message.sessionInstanceId
    ++ (encodeUIntLE 2 message.marketId
    ++ (encodeUInt 1 message.tradSesMode
    ++ (Alpha.encode message.defaultCstmApplVerId
    ++ (Alpha.encode message.defaultCstmApplVerSubId
    ++ (Alpha.encode message.pad2v2)))))))))))

def decode (bytes : List UInt8) : Option (LogonResponse × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (responseHeaderComp, bytes) ← ResponseHeaderComp.decode bytes
  let (throttleTimeInterval, bytes) ← decodeUIntLE 8 bytes
  let (throttleNoMsgs, bytes) ← decodeUIntLE 4 bytes
  let (throttleDisconnectLimit, bytes) ← decodeUIntLE 4 bytes
  let (heartBtInt, bytes) ← decodeUIntLE 4 bytes
  let (sessionInstanceId, bytes) ← decodeUIntLE 4 bytes
  let (marketId, bytes) ← decodeUIntLE 2 bytes
  let (tradSesMode, bytes) ← decodeUInt 1 bytes
  let (defaultCstmApplVerId, bytes) ← Alpha.decode 30 bytes
  let (defaultCstmApplVerSubId, bytes) ← Alpha.decode 5 bytes
  let (pad2v2, bytes) ← Alpha.decode 2 bytes
  pure ({ pad2, responseHeaderComp, throttleTimeInterval, throttleNoMsgs, throttleDisconnectLimit, heartBtInt, sessionInstanceId, marketId, tradSesMode, defaultCstmApplVerId, defaultCstmApplVerSubId, pad2v2 }, bytes)

@[simp] theorem encode_length (message : LogonResponse) : (encode message).length = 90 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, ResponseHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : LogonResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LogonResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ResponseHeaderComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
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
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : LogonResponse) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end LogonResponse

/-- Logout Response: 26 bytes -/
structure LogoutResponse where
  pad2 : Alpha 2
  responseHeaderComp : ResponseHeaderComp
  deriving DecidableEq, Repr

namespace LogoutResponse

def encode (message : LogoutResponse) : List UInt8 :=
  Alpha.encode message.pad2
    ++ (ResponseHeaderComp.encode message.responseHeaderComp)

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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [ResponseHeaderComp.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : LogoutResponse) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end LogoutResponse

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
    ++ (encodeUIntLE 8 message.cxlSize
    ++ (encodeUIntLE 4 message.quoteEntryRejectReason
    ++ (encodeUInt 1 message.quoteEntryStatus
    ++ (encodeUInt 1 message.side
    ++ (Alpha.encode message.pad2)))))

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
    ++ (NrResponseHeaderMeComp.encode message.nrResponseHeaderMeComp
    ++ (encodeUIntLE 8 message.quoteId
    ++ (encodeUIntLE 8 message.quoteResponseId
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.quoteEntryAckGrpComp.val.length)
    ++ (Alpha.encode message.pad3
    ++ (encodeMany QuoteEntryAckGrpComp.encode message.quoteEntryAckGrpComp.val)))))))

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
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MassQuoteResponse) : (encode message).length ≤ 6194 := by
  have bound_quoteEntryAckGrpComp := message.quoteEntryAckGrpComp.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, NrResponseHeaderMeComp.encode_length, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const QuoteEntryAckGrpComp.encode 24 QuoteEntryAckGrpComp.encode_length]
  omega

@[simp] theorem decode_encode (message : MassQuoteResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NrResponseHeaderMeComp.decode_encode, some_bind]
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
  rw [decodeMany_bounded 1 QuoteEntryAckGrpComp.encode QuoteEntryAckGrpComp.decode QuoteEntryAckGrpComp.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.quoteEntryAckGrpComp.length_lt]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : MassQuoteResponse) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end MassQuoteResponse

/-- Modify Order Nr Response: 146 bytes -/
structure ModifyOrderNrResponse where
  pad2 : Alpha 2
  nrResponseHeaderMeComp : NrResponseHeaderMeComp
  orderId : BitVec 64
  clOrdId : BitVec 64
  origClOrdId : BitVec 64
  securityId : BitVec 64
  execId : BitVec 64
  stopPx : BitVec 64
  leavesQty : BitVec 64
  cumQty : BitVec 64
  cxlQty : BitVec 64
  displayQty : BitVec 64
  orderIdSfx : BitVec 32
  ordStatus : OrdStatus
  execType : ExecType
  execRestatementReason : BitVec 16
  crossedIndicator : BitVec 8
  triggered : BitVec 8
  transactionDelayIndicator : BitVec 8
  pad5 : Alpha 5
  deriving DecidableEq, Repr

namespace ModifyOrderNrResponse

def encode (message : ModifyOrderNrResponse) : List UInt8 :=
  Alpha.encode message.pad2
    ++ (NrResponseHeaderMeComp.encode message.nrResponseHeaderMeComp
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 8 message.origClOrdId
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.execId
    ++ (encodeUIntLE 8 message.stopPx
    ++ (encodeUIntLE 8 message.leavesQty
    ++ (encodeUIntLE 8 message.cumQty
    ++ (encodeUIntLE 8 message.cxlQty
    ++ (encodeUIntLE 8 message.displayQty
    ++ (encodeUIntLE 4 message.orderIdSfx
    ++ (OrdStatus.encode message.ordStatus
    ++ (ExecType.encode message.execType
    ++ (encodeUIntLE 2 message.execRestatementReason
    ++ (encodeUInt 1 message.crossedIndicator
    ++ (encodeUInt 1 message.triggered
    ++ (encodeUInt 1 message.transactionDelayIndicator
    ++ (Alpha.encode message.pad5)))))))))))))))))))

def decode (bytes : List UInt8) : Option (ModifyOrderNrResponse × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (nrResponseHeaderMeComp, bytes) ← NrResponseHeaderMeComp.decode bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (origClOrdId, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  let (stopPx, bytes) ← decodeUIntLE 8 bytes
  let (leavesQty, bytes) ← decodeUIntLE 8 bytes
  let (cumQty, bytes) ← decodeUIntLE 8 bytes
  let (cxlQty, bytes) ← decodeUIntLE 8 bytes
  let (displayQty, bytes) ← decodeUIntLE 8 bytes
  let (orderIdSfx, bytes) ← decodeUIntLE 4 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (execRestatementReason, bytes) ← decodeUIntLE 2 bytes
  let (crossedIndicator, bytes) ← decodeUInt 1 bytes
  let (triggered, bytes) ← decodeUInt 1 bytes
  let (transactionDelayIndicator, bytes) ← decodeUInt 1 bytes
  let (pad5, bytes) ← Alpha.decode 5 bytes
  pure ({ pad2, nrResponseHeaderMeComp, orderId, clOrdId, origClOrdId, securityId, execId, stopPx, leavesQty, cumQty, cxlQty, displayQty, orderIdSfx, ordStatus, execType, execRestatementReason, crossedIndicator, triggered, transactionDelayIndicator, pad5 }, bytes)

@[simp] theorem encode_length (message : ModifyOrderNrResponse) : (encode message).length = 146 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, NrResponseHeaderMeComp.encode_length, encodeUIntLE_length, OrdStatus.encode_length, ExecType.encode_length, encodeUInt_length]

theorem encode_length_pos (message : ModifyOrderNrResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ModifyOrderNrResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NrResponseHeaderMeComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, OrdStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExecType.decode_encode, some_bind]
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

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : ModifyOrderNrResponse) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end ModifyOrderNrResponse

/-- Modify Order Response: 170 bytes -/
structure ModifyOrderResponse where
  pad2 : Alpha 2
  responseHeaderMeComp : ResponseHeaderMeComp
  orderId : BitVec 64
  clOrdId : BitVec 64
  origClOrdId : BitVec 64
  securityId : BitVec 64
  execId : BitVec 64
  stopPx : BitVec 64
  leavesQty : BitVec 64
  cumQty : BitVec 64
  cxlQty : BitVec 64
  displayQty : BitVec 64
  trdRegTsTimePriority : BitVec 64
  orderIdSfx : BitVec 32
  ordStatus : OrdStatus
  execType : ExecType
  execRestatementReason : BitVec 16
  crossedIndicator : BitVec 8
  triggered : BitVec 8
  transactionDelayIndicator : BitVec 8
  pad5 : Alpha 5
  deriving DecidableEq, Repr

namespace ModifyOrderResponse

def encode (message : ModifyOrderResponse) : List UInt8 :=
  Alpha.encode message.pad2
    ++ (ResponseHeaderMeComp.encode message.responseHeaderMeComp
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 8 message.origClOrdId
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.execId
    ++ (encodeUIntLE 8 message.stopPx
    ++ (encodeUIntLE 8 message.leavesQty
    ++ (encodeUIntLE 8 message.cumQty
    ++ (encodeUIntLE 8 message.cxlQty
    ++ (encodeUIntLE 8 message.displayQty
    ++ (encodeUIntLE 8 message.trdRegTsTimePriority
    ++ (encodeUIntLE 4 message.orderIdSfx
    ++ (OrdStatus.encode message.ordStatus
    ++ (ExecType.encode message.execType
    ++ (encodeUIntLE 2 message.execRestatementReason
    ++ (encodeUInt 1 message.crossedIndicator
    ++ (encodeUInt 1 message.triggered
    ++ (encodeUInt 1 message.transactionDelayIndicator
    ++ (Alpha.encode message.pad5))))))))))))))))))))

def decode (bytes : List UInt8) : Option (ModifyOrderResponse × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (responseHeaderMeComp, bytes) ← ResponseHeaderMeComp.decode bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (origClOrdId, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  let (stopPx, bytes) ← decodeUIntLE 8 bytes
  let (leavesQty, bytes) ← decodeUIntLE 8 bytes
  let (cumQty, bytes) ← decodeUIntLE 8 bytes
  let (cxlQty, bytes) ← decodeUIntLE 8 bytes
  let (displayQty, bytes) ← decodeUIntLE 8 bytes
  let (trdRegTsTimePriority, bytes) ← decodeUIntLE 8 bytes
  let (orderIdSfx, bytes) ← decodeUIntLE 4 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (execRestatementReason, bytes) ← decodeUIntLE 2 bytes
  let (crossedIndicator, bytes) ← decodeUInt 1 bytes
  let (triggered, bytes) ← decodeUInt 1 bytes
  let (transactionDelayIndicator, bytes) ← decodeUInt 1 bytes
  let (pad5, bytes) ← Alpha.decode 5 bytes
  pure ({ pad2, responseHeaderMeComp, orderId, clOrdId, origClOrdId, securityId, execId, stopPx, leavesQty, cumQty, cxlQty, displayQty, trdRegTsTimePriority, orderIdSfx, ordStatus, execType, execRestatementReason, crossedIndicator, triggered, transactionDelayIndicator, pad5 }, bytes)

@[simp] theorem encode_length (message : ModifyOrderResponse) : (encode message).length = 170 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, ResponseHeaderMeComp.encode_length, encodeUIntLE_length, OrdStatus.encode_length, ExecType.encode_length, encodeUInt_length]

theorem encode_length_pos (message : ModifyOrderResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ModifyOrderResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ResponseHeaderMeComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, OrdStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExecType.decode_encode, some_bind]
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

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : ModifyOrderResponse) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end ModifyOrderResponse

/-- New Order Nr Response: 98 bytes -/
structure NewOrderNrResponse where
  pad2 : Alpha 2
  nrResponseHeaderMeComp : NrResponseHeaderMeComp
  orderId : BitVec 64
  clOrdId : BitVec 64
  securityId : BitVec 64
  execId : BitVec 64
  orderIdSfx : BitVec 32
  ordStatus : OrdStatus
  execType : ExecType
  execRestatementReason : BitVec 16
  crossedIndicator : BitVec 8
  triggered : BitVec 8
  transactionDelayIndicator : BitVec 8
  pad5 : Alpha 5
  deriving DecidableEq, Repr

namespace NewOrderNrResponse

def encode (message : NewOrderNrResponse) : List UInt8 :=
  Alpha.encode message.pad2
    ++ (NrResponseHeaderMeComp.encode message.nrResponseHeaderMeComp
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.execId
    ++ (encodeUIntLE 4 message.orderIdSfx
    ++ (OrdStatus.encode message.ordStatus
    ++ (ExecType.encode message.execType
    ++ (encodeUIntLE 2 message.execRestatementReason
    ++ (encodeUInt 1 message.crossedIndicator
    ++ (encodeUInt 1 message.triggered
    ++ (encodeUInt 1 message.transactionDelayIndicator
    ++ (Alpha.encode message.pad5)))))))))))))

def decode (bytes : List UInt8) : Option (NewOrderNrResponse × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (nrResponseHeaderMeComp, bytes) ← NrResponseHeaderMeComp.decode bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  let (orderIdSfx, bytes) ← decodeUIntLE 4 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (execRestatementReason, bytes) ← decodeUIntLE 2 bytes
  let (crossedIndicator, bytes) ← decodeUInt 1 bytes
  let (triggered, bytes) ← decodeUInt 1 bytes
  let (transactionDelayIndicator, bytes) ← decodeUInt 1 bytes
  let (pad5, bytes) ← Alpha.decode 5 bytes
  pure ({ pad2, nrResponseHeaderMeComp, orderId, clOrdId, securityId, execId, orderIdSfx, ordStatus, execType, execRestatementReason, crossedIndicator, triggered, transactionDelayIndicator, pad5 }, bytes)

@[simp] theorem encode_length (message : NewOrderNrResponse) : (encode message).length = 98 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, NrResponseHeaderMeComp.encode_length, encodeUIntLE_length, OrdStatus.encode_length, ExecType.encode_length, encodeUInt_length]

theorem encode_length_pos (message : NewOrderNrResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NewOrderNrResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NrResponseHeaderMeComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, OrdStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExecType.decode_encode, some_bind]
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

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : NewOrderNrResponse) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end NewOrderNrResponse

/-- New Order Response: 130 bytes -/
structure NewOrderResponse where
  pad2 : Alpha 2
  responseHeaderMeComp : ResponseHeaderMeComp
  orderId : BitVec 64
  clOrdId : BitVec 64
  securityId : BitVec 64
  execId : BitVec 64
  trdRegTsEntryTime : BitVec 64
  trdRegTsTimePriority : BitVec 64
  orderIdSfx : BitVec 32
  ordStatus : OrdStatus
  execType : ExecType
  execRestatementReason : BitVec 16
  crossedIndicator : BitVec 8
  triggered : BitVec 8
  transactionDelayIndicator : BitVec 8
  pad5 : Alpha 5
  deriving DecidableEq, Repr

namespace NewOrderResponse

def encode (message : NewOrderResponse) : List UInt8 :=
  Alpha.encode message.pad2
    ++ (ResponseHeaderMeComp.encode message.responseHeaderMeComp
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.execId
    ++ (encodeUIntLE 8 message.trdRegTsEntryTime
    ++ (encodeUIntLE 8 message.trdRegTsTimePriority
    ++ (encodeUIntLE 4 message.orderIdSfx
    ++ (OrdStatus.encode message.ordStatus
    ++ (ExecType.encode message.execType
    ++ (encodeUIntLE 2 message.execRestatementReason
    ++ (encodeUInt 1 message.crossedIndicator
    ++ (encodeUInt 1 message.triggered
    ++ (encodeUInt 1 message.transactionDelayIndicator
    ++ (Alpha.encode message.pad5)))))))))))))))

def decode (bytes : List UInt8) : Option (NewOrderResponse × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (responseHeaderMeComp, bytes) ← ResponseHeaderMeComp.decode bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  let (trdRegTsEntryTime, bytes) ← decodeUIntLE 8 bytes
  let (trdRegTsTimePriority, bytes) ← decodeUIntLE 8 bytes
  let (orderIdSfx, bytes) ← decodeUIntLE 4 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (execRestatementReason, bytes) ← decodeUIntLE 2 bytes
  let (crossedIndicator, bytes) ← decodeUInt 1 bytes
  let (triggered, bytes) ← decodeUInt 1 bytes
  let (transactionDelayIndicator, bytes) ← decodeUInt 1 bytes
  let (pad5, bytes) ← Alpha.decode 5 bytes
  pure ({ pad2, responseHeaderMeComp, orderId, clOrdId, securityId, execId, trdRegTsEntryTime, trdRegTsTimePriority, orderIdSfx, ordStatus, execType, execRestatementReason, crossedIndicator, triggered, transactionDelayIndicator, pad5 }, bytes)

@[simp] theorem encode_length (message : NewOrderResponse) : (encode message).length = 130 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, ResponseHeaderMeComp.encode_length, encodeUIntLE_length, OrdStatus.encode_length, ExecType.encode_length, encodeUInt_length]

theorem encode_length_pos (message : NewOrderResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NewOrderResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ResponseHeaderMeComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, OrdStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExecType.decode_encode, some_bind]
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

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : NewOrderResponse) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end NewOrderResponse

/-- News Broadcast -/
structure NewsBroadcast where
  pad2 : Alpha 2
  rbcHeaderComp : RbcHeaderComp
  origTime : BitVec 64
  headline : Alpha 256
  pad6 : Alpha 6
  varText : Bounded 2 UInt8
  alignmentPadding : Capped 7
  deriving DecidableEq, Repr

namespace NewsBroadcast

def encode (message : NewsBroadcast) : List UInt8 :=
  Alpha.encode message.pad2
    ++ (RbcHeaderComp.encode message.rbcHeaderComp
    ++ (encodeUIntLE 8 message.origTime
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.varText.val.length)
    ++ (Alpha.encode message.headline
    ++ (Alpha.encode message.pad6
    ++ (encodeMany Byte.encode message.varText.val
    ++ (message.alignmentPadding.val)))))))

def decode (bytes : List UInt8) : Option NewsBroadcast := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderComp, bytes) ← RbcHeaderComp.decode bytes
  let (origTime, bytes) ← decodeUIntLE 8 bytes
  let (varTextLen, bytes) ← decodeUIntLE 2 bytes
  let (headline, bytes) ← Alpha.decode 256 bytes
  let (pad6, bytes) ← Alpha.decode 6 bytes
  let (varText_, bytes) ← decodeMany Byte.decode varTextLen.toNat bytes
  let alignmentPadding_ := bytes
  if fits_varText : varText_.length < 256 ^ 2 then
    if fits_alignmentPadding : alignmentPadding_.length ≤ 7 then
      pure { pad2, rbcHeaderComp, origTime, headline, pad6, varText := ⟨varText_, fits_varText⟩, alignmentPadding := ⟨alignmentPadding_, fits_alignmentPadding⟩ }
    else none
  else none

theorem encode_length_pos (message : NewsBroadcast) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : NewsBroadcast) : (encode message).length ≤ 65848 := by
  have bound_varText := message.varText.length_lt
  have bound_alignmentPadding := message.alignmentPadding.length_le
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, RbcHeaderComp.encode_length, encodeUIntLE_length, encodeMany_length_const Byte.encode 1 Byte.encode_length]
  omega

theorem decode_encode (message : NewsBroadcast) : decode (encode message) = some message := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  dsimp only
  rw [RbcHeaderComp.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 Byte.encode Byte.decode Byte.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.varText.length_lt, dite_eq_left message.alignmentPadding.length_le]
  rfl

end NewsBroadcast

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
    ++ (encodeUIntLE 8 message.fillQty
    ++ (encodeUIntLE 4 message.fillMatchId
    ++ (encodeUIntLE 4 message.fillExecId
    ++ (encodeUInt 1 message.fillLiquidityInd
    ++ (Alpha.encode message.pad7)))))

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

end FillsGrpComp

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
  displayQty : BitVec 64
  marketSegmentId : BitVec 32
  orderIdSfx : BitVec 32
  execRestatementReason : BitVec 16
  side : BitVec 8
  ordStatus : OrdStatus
  execType : ExecType
  orderEventType : BitVec 8
  matchType : BitVec 8
  triggered : BitVec 8
  crossedIndicator : BitVec 8
  fixClOrdId : Alpha 20
  pad2v2 : Alpha 2
  fillsGrpComp : Bounded 1 FillsGrpComp
  deriving DecidableEq, Repr

namespace OrderExecNotification

def encode (message : OrderExecNotification) : List UInt8 :=
  Alpha.encode message.pad2
    ++ (RbcHeaderMeComp.encode message.rbcHeaderMeComp
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 8 message.origClOrdId
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.execId
    ++ (encodeUIntLE 8 message.leavesQty
    ++ (encodeUIntLE 8 message.cumQty
    ++ (encodeUIntLE 8 message.cxlQty
    ++ (encodeUIntLE 8 message.displayQty
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.orderIdSfx
    ++ (encodeUIntLE 2 message.execRestatementReason
    ++ (encodeUInt 1 message.side
    ++ (OrdStatus.encode message.ordStatus
    ++ (ExecType.encode message.execType
    ++ (encodeUInt 1 message.orderEventType
    ++ (encodeUInt 1 message.matchType
    ++ (encodeUInt 1 message.triggered
    ++ (encodeUInt 1 message.crossedIndicator
    ++ (Alpha.encode message.fixClOrdId
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.fillsGrpComp.val.length)
    ++ (Alpha.encode message.pad2v2
    ++ (encodeMany FillsGrpComp.encode message.fillsGrpComp.val))))))))))))))))))))))))

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
  let (displayQty, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (orderIdSfx, bytes) ← decodeUIntLE 4 bytes
  let (execRestatementReason, bytes) ← decodeUIntLE 2 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (orderEventType, bytes) ← decodeUInt 1 bytes
  let (matchType, bytes) ← decodeUInt 1 bytes
  let (triggered, bytes) ← decodeUInt 1 bytes
  let (crossedIndicator, bytes) ← decodeUInt 1 bytes
  let (fixClOrdId, bytes) ← Alpha.decode 20 bytes
  let (noFills, bytes) ← decodeUInt 1 bytes
  let (pad2v2, bytes) ← Alpha.decode 2 bytes
  let (fillsGrpComp_, bytes) ← decodeMany FillsGrpComp.decode noFills.toNat bytes
  if fits_fillsGrpComp : fillsGrpComp_.length < 256 ^ 1 then
    pure ({ pad2, rbcHeaderMeComp, orderId, clOrdId, origClOrdId, securityId, execId, leavesQty, cumQty, cxlQty, displayQty, marketSegmentId, orderIdSfx, execRestatementReason, side, ordStatus, execType, orderEventType, matchType, triggered, crossedIndicator, fixClOrdId, pad2v2, fillsGrpComp := ⟨fillsGrpComp_, fits_fillsGrpComp⟩ }, bytes)
  else none

theorem encode_length_pos (message : OrderExecNotification) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : OrderExecNotification) : (encode message).length ≤ 8330 := by
  have bound_fillsGrpComp := message.fillsGrpComp.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, RbcHeaderMeComp.encode_length, encodeUIntLE_length, encodeUInt_length, OrdStatus.encode_length, ExecType.encode_length, encodeMany_length_const FillsGrpComp.encode 32 FillsGrpComp.encode_length]
  omega

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : OrderExecNotification) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RbcHeaderMeComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
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
  rw [List.append_assoc, OrdStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExecType.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 FillsGrpComp.encode FillsGrpComp.decode FillsGrpComp.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.fillsGrpComp.length_lt]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : OrderExecNotification) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end OrderExecNotification

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
  displayQty : BitVec 64
  displayLowQty : BitVec 64
  displayHighQty : BitVec 64
  stopPx : BitVec 64
  volumeDiscoveryPrice : BitVec 64
  pegOffsetValueAbs : BitVec 64
  pegOffsetValuePct : BitVec 64
  quoteId : BitVec 64
  marketSegmentId : BitVec 32
  orderIdSfx : BitVec 32
  expireDate : BitVec 32
  matchInstCrossId : BitVec 32
  partyIdExecutingUnit : BitVec 32
  partyIdSessionId : BitVec 32
  partyIdExecutingTrader : BitVec 32
  partyIdEnteringTrader : BitVec 32
  execRestatementReason : BitVec 16
  partyIdEnteringFirm : BitVec 8
  ordStatus : OrdStatus
  execType : ExecType
  orderEventType : BitVec 8
  matchType : BitVec 8
  side : BitVec 8
  ordType : BitVec 8
  tradingCapacity : BitVec 8
  timeInForce : BitVec 8
  execInst : BitVec 8
  tradingSessionSubId : BitVec 8
  applSeqIndicator : BitVec 8
  exDestinationType : BitVec 8
  partyEnteringFirm : Alpha 5
  partyEnteringTrader : Alpha 6
  partyExecutingFirm : Alpha 5
  partyExecutingTrader : Alpha 6
  freeText1 : Alpha 12
  freeText2 : Alpha 12
  freeText4 : Alpha 16
  fixClOrdId : Alpha 20
  triggered : BitVec 8
  crossedIndicator : BitVec 8
  pad4 : Alpha 4
  fillsGrpComp : Bounded 1 FillsGrpComp
  deriving DecidableEq, Repr

namespace OrderExecReportBroadcast

def encode (message : OrderExecReportBroadcast) : List UInt8 :=
  Alpha.encode message.pad2
    ++ (RbcHeaderMeComp.encode message.rbcHeaderMeComp
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 8 message.origClOrdId
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.execId
    ++ (encodeUIntLE 8 message.trdRegTsEntryTime
    ++ (encodeUIntLE 8 message.trdRegTsTimePriority
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 8 message.leavesQty
    ++ (encodeUIntLE 8 message.cumQty
    ++ (encodeUIntLE 8 message.cxlQty
    ++ (encodeUIntLE 8 message.orderQty
    ++ (encodeUIntLE 8 message.displayQty
    ++ (encodeUIntLE 8 message.displayLowQty
    ++ (encodeUIntLE 8 message.displayHighQty
    ++ (encodeUIntLE 8 message.stopPx
    ++ (encodeUIntLE 8 message.volumeDiscoveryPrice
    ++ (encodeUIntLE 8 message.pegOffsetValueAbs
    ++ (encodeUIntLE 8 message.pegOffsetValuePct
    ++ (encodeUIntLE 8 message.quoteId
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.orderIdSfx
    ++ (encodeUIntLE 4 message.expireDate
    ++ (encodeUIntLE 4 message.matchInstCrossId
    ++ (encodeUIntLE 4 message.partyIdExecutingUnit
    ++ (encodeUIntLE 4 message.partyIdSessionId
    ++ (encodeUIntLE 4 message.partyIdExecutingTrader
    ++ (encodeUIntLE 4 message.partyIdEnteringTrader
    ++ (encodeUIntLE 2 message.execRestatementReason
    ++ (encodeUInt 1 message.partyIdEnteringFirm
    ++ (OrdStatus.encode message.ordStatus
    ++ (ExecType.encode message.execType
    ++ (encodeUInt 1 message.orderEventType
    ++ (encodeUInt 1 message.matchType
    ++ (encodeUInt 1 message.side
    ++ (encodeUInt 1 message.ordType
    ++ (encodeUInt 1 message.tradingCapacity
    ++ (encodeUInt 1 message.timeInForce
    ++ (encodeUInt 1 message.execInst
    ++ (encodeUInt 1 message.tradingSessionSubId
    ++ (encodeUInt 1 message.applSeqIndicator
    ++ (encodeUInt 1 message.exDestinationType
    ++ (Alpha.encode message.partyEnteringFirm
    ++ (Alpha.encode message.partyEnteringTrader
    ++ (Alpha.encode message.partyExecutingFirm
    ++ (Alpha.encode message.partyExecutingTrader
    ++ (Alpha.encode message.freeText1
    ++ (Alpha.encode message.freeText2
    ++ (Alpha.encode message.freeText4
    ++ (Alpha.encode message.fixClOrdId
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.fillsGrpComp.val.length)
    ++ (encodeUInt 1 message.triggered
    ++ (encodeUInt 1 message.crossedIndicator
    ++ (Alpha.encode message.pad4
    ++ (encodeMany FillsGrpComp.encode message.fillsGrpComp.val))))))))))))))))))))))))))))))))))))))))))))))))))))))))

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
  let (displayQty, bytes) ← decodeUIntLE 8 bytes
  let (displayLowQty, bytes) ← decodeUIntLE 8 bytes
  let (displayHighQty, bytes) ← decodeUIntLE 8 bytes
  let (stopPx, bytes) ← decodeUIntLE 8 bytes
  let (volumeDiscoveryPrice, bytes) ← decodeUIntLE 8 bytes
  let (pegOffsetValueAbs, bytes) ← decodeUIntLE 8 bytes
  let (pegOffsetValuePct, bytes) ← decodeUIntLE 8 bytes
  let (quoteId, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (orderIdSfx, bytes) ← decodeUIntLE 4 bytes
  let (expireDate, bytes) ← decodeUIntLE 4 bytes
  let (matchInstCrossId, bytes) ← decodeUIntLE 4 bytes
  let (partyIdExecutingUnit, bytes) ← decodeUIntLE 4 bytes
  let (partyIdSessionId, bytes) ← decodeUIntLE 4 bytes
  let (partyIdExecutingTrader, bytes) ← decodeUIntLE 4 bytes
  let (partyIdEnteringTrader, bytes) ← decodeUIntLE 4 bytes
  let (execRestatementReason, bytes) ← decodeUIntLE 2 bytes
  let (partyIdEnteringFirm, bytes) ← decodeUInt 1 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (orderEventType, bytes) ← decodeUInt 1 bytes
  let (matchType, bytes) ← decodeUInt 1 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (ordType, bytes) ← decodeUInt 1 bytes
  let (tradingCapacity, bytes) ← decodeUInt 1 bytes
  let (timeInForce, bytes) ← decodeUInt 1 bytes
  let (execInst, bytes) ← decodeUInt 1 bytes
  let (tradingSessionSubId, bytes) ← decodeUInt 1 bytes
  let (applSeqIndicator, bytes) ← decodeUInt 1 bytes
  let (exDestinationType, bytes) ← decodeUInt 1 bytes
  let (partyEnteringFirm, bytes) ← Alpha.decode 5 bytes
  let (partyEnteringTrader, bytes) ← Alpha.decode 6 bytes
  let (partyExecutingFirm, bytes) ← Alpha.decode 5 bytes
  let (partyExecutingTrader, bytes) ← Alpha.decode 6 bytes
  let (freeText1, bytes) ← Alpha.decode 12 bytes
  let (freeText2, bytes) ← Alpha.decode 12 bytes
  let (freeText4, bytes) ← Alpha.decode 16 bytes
  let (fixClOrdId, bytes) ← Alpha.decode 20 bytes
  let (noFills, bytes) ← decodeUInt 1 bytes
  let (triggered, bytes) ← decodeUInt 1 bytes
  let (crossedIndicator, bytes) ← decodeUInt 1 bytes
  let (pad4, bytes) ← Alpha.decode 4 bytes
  let (fillsGrpComp_, bytes) ← decodeMany FillsGrpComp.decode noFills.toNat bytes
  if fits_fillsGrpComp : fillsGrpComp_.length < 256 ^ 1 then
    pure ({ pad2, rbcHeaderMeComp, orderId, clOrdId, origClOrdId, securityId, execId, trdRegTsEntryTime, trdRegTsTimePriority, price, leavesQty, cumQty, cxlQty, orderQty, displayQty, displayLowQty, displayHighQty, stopPx, volumeDiscoveryPrice, pegOffsetValueAbs, pegOffsetValuePct, quoteId, marketSegmentId, orderIdSfx, expireDate, matchInstCrossId, partyIdExecutingUnit, partyIdSessionId, partyIdExecutingTrader, partyIdEnteringTrader, execRestatementReason, partyIdEnteringFirm, ordStatus, execType, orderEventType, matchType, side, ordType, tradingCapacity, timeInForce, execInst, tradingSessionSubId, applSeqIndicator, exDestinationType, partyEnteringFirm, partyEnteringTrader, partyExecutingFirm, partyExecutingTrader, freeText1, freeText2, freeText4, fixClOrdId, triggered, crossedIndicator, pad4, fillsGrpComp := ⟨fillsGrpComp_, fits_fillsGrpComp⟩ }, bytes)
  else none

theorem encode_length_pos (message : OrderExecReportBroadcast) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : OrderExecReportBroadcast) : (encode message).length ≤ 8514 := by
  have bound_fillsGrpComp := message.fillsGrpComp.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, RbcHeaderMeComp.encode_length, encodeUIntLE_length, encodeUInt_length, OrdStatus.encode_length, ExecType.encode_length, encodeMany_length_const FillsGrpComp.encode 32 FillsGrpComp.encode_length]
  omega

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : OrderExecReportBroadcast) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RbcHeaderMeComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
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
  rw [List.append_assoc, OrdStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExecType.decode_encode, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 FillsGrpComp.encode FillsGrpComp.decode FillsGrpComp.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.fillsGrpComp.length_lt]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : OrderExecReportBroadcast) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

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
  displayQty : BitVec 64
  marketSegmentId : BitVec 32
  orderIdSfx : BitVec 32
  execRestatementReason : BitVec 16
  side : BitVec 8
  ordStatus : OrdStatus
  execType : ExecType
  matchType : BitVec 8
  triggered : BitVec 8
  crossedIndicator : BitVec 8
  transactionDelayIndicator : BitVec 8
  pad6 : Alpha 6
  fillsGrpComp : Bounded 1 FillsGrpComp
  deriving DecidableEq, Repr

namespace OrderExecResponse

def encode (message : OrderExecResponse) : List UInt8 :=
  Alpha.encode message.pad2
    ++ (ResponseHeaderMeComp.encode message.responseHeaderMeComp
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 8 message.origClOrdId
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.execId
    ++ (encodeUIntLE 8 message.trdRegTsEntryTime
    ++ (encodeUIntLE 8 message.trdRegTsTimePriority
    ++ (encodeUIntLE 8 message.leavesQty
    ++ (encodeUIntLE 8 message.cumQty
    ++ (encodeUIntLE 8 message.cxlQty
    ++ (encodeUIntLE 8 message.displayQty
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.orderIdSfx
    ++ (encodeUIntLE 2 message.execRestatementReason
    ++ (encodeUInt 1 message.side
    ++ (OrdStatus.encode message.ordStatus
    ++ (ExecType.encode message.execType
    ++ (encodeUInt 1 message.matchType
    ++ (encodeUInt 1 message.triggered
    ++ (encodeUInt 1 message.crossedIndicator
    ++ (encodeUInt 1 message.transactionDelayIndicator
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.fillsGrpComp.val.length)
    ++ (Alpha.encode message.pad6
    ++ (encodeMany FillsGrpComp.encode message.fillsGrpComp.val)))))))))))))))))))))))))

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
  let (displayQty, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (orderIdSfx, bytes) ← decodeUIntLE 4 bytes
  let (execRestatementReason, bytes) ← decodeUIntLE 2 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (matchType, bytes) ← decodeUInt 1 bytes
  let (triggered, bytes) ← decodeUInt 1 bytes
  let (crossedIndicator, bytes) ← decodeUInt 1 bytes
  let (transactionDelayIndicator, bytes) ← decodeUInt 1 bytes
  let (noFills, bytes) ← decodeUInt 1 bytes
  let (pad6, bytes) ← Alpha.decode 6 bytes
  let (fillsGrpComp_, bytes) ← decodeMany FillsGrpComp.decode noFills.toNat bytes
  if fits_fillsGrpComp : fillsGrpComp_.length < 256 ^ 1 then
    pure ({ pad2, responseHeaderMeComp, orderId, clOrdId, origClOrdId, securityId, execId, trdRegTsEntryTime, trdRegTsTimePriority, leavesQty, cumQty, cxlQty, displayQty, marketSegmentId, orderIdSfx, execRestatementReason, side, ordStatus, execType, matchType, triggered, crossedIndicator, transactionDelayIndicator, pad6, fillsGrpComp := ⟨fillsGrpComp_, fits_fillsGrpComp⟩ }, bytes)
  else none

theorem encode_length_pos (message : OrderExecResponse) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : OrderExecResponse) : (encode message).length ≤ 8338 := by
  have bound_fillsGrpComp := message.fillsGrpComp.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, ResponseHeaderMeComp.encode_length, encodeUIntLE_length, encodeUInt_length, OrdStatus.encode_length, ExecType.encode_length, encodeMany_length_const FillsGrpComp.encode 32 FillsGrpComp.encode_length]
  omega

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : OrderExecResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ResponseHeaderMeComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
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
  rw [List.append_assoc, OrdStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExecType.decode_encode, some_bind]
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
  rw [decodeMany_bounded 1 FillsGrpComp.encode FillsGrpComp.decode FillsGrpComp.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.fillsGrpComp.length_lt]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : OrderExecResponse) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

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
    ++ (RbcHeaderComp.encode message.rbcHeaderComp
    ++ (encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 4 message.tradeDate
    ++ (encodeUIntLE 4 message.requestingPartyIdExecutingTrader
    ++ (encodeUIntLE 4 message.partyIdExecutingUnit
    ++ (encodeUIntLE 4 message.partyIdExecutingTrader
    ++ (encodeUIntLE 4 message.requestingPartyIdExecutingSystem
    ++ (encodeUIntLE 2 message.marketId
    ++ (encodeUInt 1 message.partyActionType
    ++ (encodeUInt 1 message.requestingPartyIdEnteringFirm))))))))))

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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RbcHeaderComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : PartyActionReport) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

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
    ++ (RbcHeaderComp.encode message.rbcHeaderComp
    ++ (encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 4 message.tradeDate
    ++ (encodeUIntLE 4 message.partyDetailIdExecutingUnit
    ++ (encodeUIntLE 4 message.requestingPartyIdExecutingSystem
    ++ (encodeUIntLE 2 message.marketId
    ++ (ListUpdateAction.encode message.listUpdateAction
    ++ (Alpha.encode message.requestingPartyEnteringFirm
    ++ (Alpha.encode message.requestingPartyClearingFirm
    ++ (encodeUInt 1 message.partyDetailStatus
    ++ (Alpha.encode message.pad6)))))))))))

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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RbcHeaderComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, ListUpdateAction.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : PartyEntitlementsUpdateReport) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end PartyEntitlementsUpdateReport

/-- Quote Activation Notification -/
structure QuoteActivationNotification where
  pad2 : Alpha 2
  rbcHeaderMeComp : RbcHeaderMeComp
  massActionReportId : BitVec 64
  marketSegmentId : BitVec 32
  partyIdEnteringTrader : BitVec 32
  partyIdEnteringFirm : BitVec 8
  massActionType : BitVec 8
  massActionReason : BitVec 8
  pad3 : Alpha 3
  notAffectedSecuritiesGrpComp : Bounded 2 NotAffectedSecuritiesGrpComp
  deriving DecidableEq, Repr

namespace QuoteActivationNotification

def encode (message : QuoteActivationNotification) : List UInt8 :=
  Alpha.encode message.pad2
    ++ (RbcHeaderMeComp.encode message.rbcHeaderMeComp
    ++ (encodeUIntLE 8 message.massActionReportId
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.partyIdEnteringTrader
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.notAffectedSecuritiesGrpComp.val.length)
    ++ (encodeUInt 1 message.partyIdEnteringFirm
    ++ (encodeUInt 1 message.massActionType
    ++ (encodeUInt 1 message.massActionReason
    ++ (Alpha.encode message.pad3
    ++ (encodeMany NotAffectedSecuritiesGrpComp.encode message.notAffectedSecuritiesGrpComp.val))))))))))

def decode (bytes : List UInt8) : Option (QuoteActivationNotification × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderMeComp, bytes) ← RbcHeaderMeComp.decode bytes
  let (massActionReportId, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (partyIdEnteringTrader, bytes) ← decodeUIntLE 4 bytes
  let (noNotAffectedSecurities, bytes) ← decodeUIntLE 2 bytes
  let (partyIdEnteringFirm, bytes) ← decodeUInt 1 bytes
  let (massActionType, bytes) ← decodeUInt 1 bytes
  let (massActionReason, bytes) ← decodeUInt 1 bytes
  let (pad3, bytes) ← Alpha.decode 3 bytes
  let (notAffectedSecuritiesGrpComp_, bytes) ← decodeMany NotAffectedSecuritiesGrpComp.decode noNotAffectedSecurities.toNat bytes
  if fits_notAffectedSecuritiesGrpComp : notAffectedSecuritiesGrpComp_.length < 256 ^ 2 then
    pure ({ pad2, rbcHeaderMeComp, massActionReportId, marketSegmentId, partyIdEnteringTrader, partyIdEnteringFirm, massActionType, massActionReason, pad3, notAffectedSecuritiesGrpComp := ⟨notAffectedSecuritiesGrpComp_, fits_notAffectedSecuritiesGrpComp⟩ }, bytes)
  else none

theorem encode_length_pos (message : QuoteActivationNotification) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : QuoteActivationNotification) : (encode message).length ≤ 524362 := by
  have bound_notAffectedSecuritiesGrpComp := message.notAffectedSecuritiesGrpComp.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, RbcHeaderMeComp.encode_length, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const NotAffectedSecuritiesGrpComp.encode 8 NotAffectedSecuritiesGrpComp.encode_length]
  omega

@[simp] theorem decode_encode (message : QuoteActivationNotification) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RbcHeaderMeComp.decode_encode, some_bind]
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
  rw [decodeMany_bounded 2 NotAffectedSecuritiesGrpComp.encode NotAffectedSecuritiesGrpComp.decode NotAffectedSecuritiesGrpComp.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.notAffectedSecuritiesGrpComp.length_lt]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : QuoteActivationNotification) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

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
    ++ (NrResponseHeaderMeComp.encode message.nrResponseHeaderMeComp
    ++ (encodeUIntLE 8 message.massActionReportId
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.notAffectedSecuritiesGrpComp.val.length)
    ++ (Alpha.encode message.pad6
    ++ (encodeMany NotAffectedSecuritiesGrpComp.encode message.notAffectedSecuritiesGrpComp.val)))))

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
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : QuoteActivationResponse) : (encode message).length ≤ 524346 := by
  have bound_notAffectedSecuritiesGrpComp := message.notAffectedSecuritiesGrpComp.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, NrResponseHeaderMeComp.encode_length, encodeUIntLE_length, encodeMany_length_const NotAffectedSecuritiesGrpComp.encode 8 NotAffectedSecuritiesGrpComp.encode_length]
  omega

@[simp] theorem decode_encode (message : QuoteActivationResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NrResponseHeaderMeComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 NotAffectedSecuritiesGrpComp.encode NotAffectedSecuritiesGrpComp.decode NotAffectedSecuritiesGrpComp.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.notAffectedSecuritiesGrpComp.length_lt]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : QuoteActivationResponse) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

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
    ++ (encodeUIntLE 8 message.quoteEventPx
    ++ (encodeUIntLE 8 message.quoteEventQty
    ++ (encodeUIntLE 8 message.quoteMsgId
    ++ (encodeUIntLE 4 message.quoteEventMatchId
    ++ (encodeUIntLE 4 message.quoteEventExecId
    ++ (encodeUInt 1 message.quoteEventType
    ++ (encodeUInt 1 message.quoteEventSide
    ++ (encodeUInt 1 message.quoteEventLiquidityInd
    ++ (encodeUInt 1 message.quoteEventReason
    ++ (Alpha.encode message.pad4))))))))))

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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
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

end QuoteEventGrpComp

/-- Quote Execution Report -/
structure QuoteExecutionReport where
  pad2 : Alpha 2
  rbcHeaderMeComp : RbcHeaderMeComp
  execId : BitVec 64
  marketSegmentId : BitVec 32
  pad3 : Alpha 3
  quoteEventGrpComp : Bounded 1 QuoteEventGrpComp
  deriving DecidableEq, Repr

namespace QuoteExecutionReport

def encode (message : QuoteExecutionReport) : List UInt8 :=
  Alpha.encode message.pad2
    ++ (RbcHeaderMeComp.encode message.rbcHeaderMeComp
    ++ (encodeUIntLE 8 message.execId
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.quoteEventGrpComp.val.length)
    ++ (Alpha.encode message.pad3
    ++ (encodeMany QuoteEventGrpComp.encode message.quoteEventGrpComp.val))))))

def decode (bytes : List UInt8) : Option (QuoteExecutionReport × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderMeComp, bytes) ← RbcHeaderMeComp.decode bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (noQuoteEvents, bytes) ← decodeUInt 1 bytes
  let (pad3, bytes) ← Alpha.decode 3 bytes
  let (quoteEventGrpComp_, bytes) ← decodeMany QuoteEventGrpComp.decode noQuoteEvents.toNat bytes
  if fits_quoteEventGrpComp : quoteEventGrpComp_.length < 256 ^ 1 then
    pure ({ pad2, rbcHeaderMeComp, execId, marketSegmentId, pad3, quoteEventGrpComp := ⟨quoteEventGrpComp_, fits_quoteEventGrpComp⟩ }, bytes)
  else none

theorem encode_length_pos (message : QuoteExecutionReport) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : QuoteExecutionReport) : (encode message).length ≤ 12314 := by
  have bound_quoteEventGrpComp := message.quoteEventGrpComp.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, RbcHeaderMeComp.encode_length, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const QuoteEventGrpComp.encode 48 QuoteEventGrpComp.encode_length]
  omega

@[simp] theorem decode_encode (message : QuoteExecutionReport) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RbcHeaderMeComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 QuoteEventGrpComp.encode QuoteEventGrpComp.decode QuoteEventGrpComp.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.quoteEventGrpComp.length_lt]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : QuoteExecutionReport) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end QuoteExecutionReport

/-- Rfq Broadcast: 98 bytes -/
structure RfqBroadcast where
  pad2 : Alpha 2
  rbcHeaderMeComp : RbcHeaderMeComp
  securityId : BitVec 64
  execId : BitVec 64
  orderQty : BitVec 64
  marketSegmentId : BitVec 32
  side : BitVec 8
  partyExecutingFirm : Alpha 5
  pad6 : Alpha 6
  deriving DecidableEq, Repr

namespace RfqBroadcast

def encode (message : RfqBroadcast) : List UInt8 :=
  Alpha.encode message.pad2
    ++ (RbcHeaderMeComp.encode message.rbcHeaderMeComp
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.execId
    ++ (encodeUIntLE 8 message.orderQty
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUInt 1 message.side
    ++ (Alpha.encode message.partyExecutingFirm
    ++ (Alpha.encode message.pad6))))))))

def decode (bytes : List UInt8) : Option (RfqBroadcast × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderMeComp, bytes) ← RbcHeaderMeComp.decode bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  let (orderQty, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (partyExecutingFirm, bytes) ← Alpha.decode 5 bytes
  let (pad6, bytes) ← Alpha.decode 6 bytes
  pure ({ pad2, rbcHeaderMeComp, securityId, execId, orderQty, marketSegmentId, side, partyExecutingFirm, pad6 }, bytes)

@[simp] theorem encode_length (message : RfqBroadcast) : (encode message).length = 98 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RbcHeaderMeComp.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : RfqBroadcast) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RfqBroadcast) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RbcHeaderMeComp.decode_encode, some_bind]
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

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : RfqBroadcast) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end RfqBroadcast

/-- Rfq Reject Notification: 98 bytes -/
structure RfqRejectNotification where
  pad2 : Alpha 2
  rbcHeaderMeComp : RbcHeaderMeComp
  securityId : BitVec 64
  execId : BitVec 64
  quoteId : BitVec 64
  marketSegmentId : BitVec 32
  quoteRequestRejectReason : BitVec 8
  partyExecutingFirm : Alpha 5
  pad6 : Alpha 6
  deriving DecidableEq, Repr

namespace RfqRejectNotification

def encode (message : RfqRejectNotification) : List UInt8 :=
  Alpha.encode message.pad2
    ++ (RbcHeaderMeComp.encode message.rbcHeaderMeComp
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.execId
    ++ (encodeUIntLE 8 message.quoteId
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUInt 1 message.quoteRequestRejectReason
    ++ (Alpha.encode message.partyExecutingFirm
    ++ (Alpha.encode message.pad6))))))))

def decode (bytes : List UInt8) : Option (RfqRejectNotification × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderMeComp, bytes) ← RbcHeaderMeComp.decode bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  let (quoteId, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (quoteRequestRejectReason, bytes) ← decodeUInt 1 bytes
  let (partyExecutingFirm, bytes) ← Alpha.decode 5 bytes
  let (pad6, bytes) ← Alpha.decode 6 bytes
  pure ({ pad2, rbcHeaderMeComp, securityId, execId, quoteId, marketSegmentId, quoteRequestRejectReason, partyExecutingFirm, pad6 }, bytes)

@[simp] theorem encode_length (message : RfqRejectNotification) : (encode message).length = 98 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RbcHeaderMeComp.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : RfqRejectNotification) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RfqRejectNotification) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RbcHeaderMeComp.decode_encode, some_bind]
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

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : RfqRejectNotification) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end RfqRejectNotification

/-- Rfq Response: 58 bytes -/
structure RfqResponse where
  pad2 : Alpha 2
  nrResponseHeaderMeComp : NrResponseHeaderMeComp
  execId : BitVec 64
  deriving DecidableEq, Repr

namespace RfqResponse

def encode (message : RfqResponse) : List UInt8 :=
  Alpha.encode message.pad2
    ++ (NrResponseHeaderMeComp.encode message.nrResponseHeaderMeComp
    ++ (encodeUIntLE 8 message.execId))

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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NrResponseHeaderMeComp.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : RfqResponse) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end RfqResponse

/-- Rfq Specialist Broadcast: 106 bytes -/
structure RfqSpecialistBroadcast where
  pad2 : Alpha 2
  rbcHeaderMeComp : RbcHeaderMeComp
  securityId : BitVec 64
  execId : BitVec 64
  orderQty : BitVec 64
  quoteId : BitVec 64
  marketSegmentId : BitVec 32
  side : BitVec 8
  partyExecutingFirm : Alpha 5
  pad6 : Alpha 6
  deriving DecidableEq, Repr

namespace RfqSpecialistBroadcast

def encode (message : RfqSpecialistBroadcast) : List UInt8 :=
  Alpha.encode message.pad2
    ++ (RbcHeaderMeComp.encode message.rbcHeaderMeComp
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.execId
    ++ (encodeUIntLE 8 message.orderQty
    ++ (encodeUIntLE 8 message.quoteId
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUInt 1 message.side
    ++ (Alpha.encode message.partyExecutingFirm
    ++ (Alpha.encode message.pad6)))))))))

def decode (bytes : List UInt8) : Option (RfqSpecialistBroadcast × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderMeComp, bytes) ← RbcHeaderMeComp.decode bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  let (orderQty, bytes) ← decodeUIntLE 8 bytes
  let (quoteId, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (partyExecutingFirm, bytes) ← Alpha.decode 5 bytes
  let (pad6, bytes) ← Alpha.decode 6 bytes
  pure ({ pad2, rbcHeaderMeComp, securityId, execId, orderQty, quoteId, marketSegmentId, side, partyExecutingFirm, pad6 }, bytes)

@[simp] theorem encode_length (message : RfqSpecialistBroadcast) : (encode message).length = 106 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RbcHeaderMeComp.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : RfqSpecialistBroadcast) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RfqSpecialistBroadcast) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RbcHeaderMeComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
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

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : RfqSpecialistBroadcast) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end RfqSpecialistBroadcast

/-- Reject -/
structure Reject where
  pad2 : Alpha 2
  nrResponseHeaderMeComp : NrResponseHeaderMeComp
  sessionRejectReason : BitVec 32
  sessionStatus : BitVec 8
  pad1 : Alpha 1
  varText : Bounded 2 UInt8
  alignmentPadding : Capped 7
  deriving DecidableEq, Repr

namespace Reject

def encode (message : Reject) : List UInt8 :=
  Alpha.encode message.pad2
    ++ (NrResponseHeaderMeComp.encode message.nrResponseHeaderMeComp
    ++ (encodeUIntLE 4 message.sessionRejectReason
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.varText.val.length)
    ++ (encodeUInt 1 message.sessionStatus
    ++ (Alpha.encode message.pad1
    ++ (encodeMany Byte.encode message.varText.val
    ++ (message.alignmentPadding.val)))))))

def decode (bytes : List UInt8) : Option Reject := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (nrResponseHeaderMeComp, bytes) ← NrResponseHeaderMeComp.decode bytes
  let (sessionRejectReason, bytes) ← decodeUIntLE 4 bytes
  let (varTextLen, bytes) ← decodeUIntLE 2 bytes
  let (sessionStatus, bytes) ← decodeUInt 1 bytes
  let (pad1, bytes) ← Alpha.decode 1 bytes
  let (varText_, bytes) ← decodeMany Byte.decode varTextLen.toNat bytes
  let alignmentPadding_ := bytes
  if fits_varText : varText_.length < 256 ^ 2 then
    if fits_alignmentPadding : alignmentPadding_.length ≤ 7 then
      pure { pad2, nrResponseHeaderMeComp, sessionRejectReason, sessionStatus, pad1, varText := ⟨varText_, fits_varText⟩, alignmentPadding := ⟨alignmentPadding_, fits_alignmentPadding⟩ }
    else none
  else none

theorem encode_length_pos (message : Reject) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : Reject) : (encode message).length ≤ 65600 := by
  have bound_varText := message.varText.length_lt
  have bound_alignmentPadding := message.alignmentPadding.length_le
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, NrResponseHeaderMeComp.encode_length, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const Byte.encode 1 Byte.encode_length]
  omega

theorem decode_encode (message : Reject) : decode (encode message) = some message := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  dsimp only
  rw [NrResponseHeaderMeComp.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 Byte.encode Byte.decode Byte.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.varText.length_lt, dite_eq_left message.alignmentPadding.length_le]
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
    ++ (ResponseHeaderComp.encode message.responseHeaderComp
    ++ (encodeUIntLE 2 message.applTotalMessageCount
    ++ (Alpha.encode message.applEndMsgId
    ++ (Alpha.encode message.refApplLastMsgId
    ++ (Alpha.encode message.pad6)))))

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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ResponseHeaderComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : RetransmitMeMessageResponse) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

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
    ++ (ResponseHeaderComp.encode message.responseHeaderComp
    ++ (encodeUIntLE 8 message.applEndSeqNum
    ++ (encodeUIntLE 8 message.refApplLastSeqNum
    ++ (encodeUIntLE 2 message.applTotalMessageCount
    ++ (Alpha.encode message.pad6)))))

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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ResponseHeaderComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : RetransmitResponse) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end RetransmitResponse

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
    ++ (encodeUIntLE 4 message.applSubId
    ++ (encodeUInt 1 message.applId
    ++ (encodeUInt 1 message.lastFragment
    ++ (Alpha.encode message.pad2))))

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
    ++ (NrbcHeaderComp.encode message.nrbcHeaderComp
    ++ (encodeUIntLE 4 message.matchingEngineTradeDate
    ++ (encodeUIntLE 4 message.tradeManagerTradeDate
    ++ (encodeUIntLE 4 message.applSeqTradeDate
    ++ (encodeUIntLE 4 message.t7EntryServiceTradeDate
    ++ (encodeUIntLE 4 message.t7EntryServiceRtmTradeDate
    ++ (encodeUIntLE 2 message.partitionId
    ++ (encodeUInt 1 message.matchingEngineStatus
    ++ (encodeUInt 1 message.tradeManagerStatus
    ++ (encodeUInt 1 message.applSeqStatus
    ++ (encodeUInt 1 message.t7EntryServiceStatus
    ++ (encodeUInt 1 message.t7EntryServiceRtmStatus
    ++ (Alpha.encode message.pad5)))))))))))))

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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NrbcHeaderComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
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
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : ServiceAvailabilityBroadcast) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end ServiceAvailabilityBroadcast

/-- Service Availability Market Broadcast: 26 bytes -/
structure ServiceAvailabilityMarketBroadcast where
  pad2 : Alpha 2
  nrbcHeaderComp : NrbcHeaderComp
  selectiveRequestForQuoteServiceTradeDate : BitVec 32
  selectiveRequestForQuoteServiceStatus : BitVec 8
  pad3 : Alpha 3
  deriving DecidableEq, Repr

namespace ServiceAvailabilityMarketBroadcast

def encode (message : ServiceAvailabilityMarketBroadcast) : List UInt8 :=
  Alpha.encode message.pad2
    ++ (NrbcHeaderComp.encode message.nrbcHeaderComp
    ++ (encodeUIntLE 4 message.selectiveRequestForQuoteServiceTradeDate
    ++ (encodeUInt 1 message.selectiveRequestForQuoteServiceStatus
    ++ (Alpha.encode message.pad3))))

def decode (bytes : List UInt8) : Option (ServiceAvailabilityMarketBroadcast × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (nrbcHeaderComp, bytes) ← NrbcHeaderComp.decode bytes
  let (selectiveRequestForQuoteServiceTradeDate, bytes) ← decodeUIntLE 4 bytes
  let (selectiveRequestForQuoteServiceStatus, bytes) ← decodeUInt 1 bytes
  let (pad3, bytes) ← Alpha.decode 3 bytes
  pure ({ pad2, nrbcHeaderComp, selectiveRequestForQuoteServiceTradeDate, selectiveRequestForQuoteServiceStatus, pad3 }, bytes)

@[simp] theorem encode_length (message : ServiceAvailabilityMarketBroadcast) : (encode message).length = 26 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, NrbcHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : ServiceAvailabilityMarketBroadcast) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ServiceAvailabilityMarketBroadcast) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NrbcHeaderComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : ServiceAvailabilityMarketBroadcast) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end ServiceAvailabilityMarketBroadcast

/-- Specialist Delete All Order Broadcast -/
structure SpecialistDeleteAllOrderBroadcast where
  pad2 : Alpha 2
  rbcHeaderMeComp : RbcHeaderMeComp
  massActionReportId : BitVec 64
  marketSegmentId : BitVec 32
  partyIdEnteringTrader : BitVec 32
  partyIdEnteringFirm : BitVec 8
  massActionReason : BitVec 8
  pad2v2 : Alpha 2
  affectedOrdGrpComp : Bounded 2 AffectedOrdGrpComp
  notAffectedOrdersGrpComp : Bounded 2 NotAffectedOrdersGrpComp
  deriving DecidableEq, Repr

namespace SpecialistDeleteAllOrderBroadcast

def encode (message : SpecialistDeleteAllOrderBroadcast) : List UInt8 :=
  Alpha.encode message.pad2
    ++ (RbcHeaderMeComp.encode message.rbcHeaderMeComp
    ++ (encodeUIntLE 8 message.massActionReportId
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.partyIdEnteringTrader
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.affectedOrdGrpComp.val.length)
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.notAffectedOrdersGrpComp.val.length)
    ++ (encodeUInt 1 message.partyIdEnteringFirm
    ++ (encodeUInt 1 message.massActionReason
    ++ (Alpha.encode message.pad2v2
    ++ (encodeMany AffectedOrdGrpComp.encode message.affectedOrdGrpComp.val
    ++ (encodeMany NotAffectedOrdersGrpComp.encode message.notAffectedOrdersGrpComp.val)))))))))))

def decode (bytes : List UInt8) : Option (SpecialistDeleteAllOrderBroadcast × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderMeComp, bytes) ← RbcHeaderMeComp.decode bytes
  let (massActionReportId, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (partyIdEnteringTrader, bytes) ← decodeUIntLE 4 bytes
  let (noAffectedOrders, bytes) ← decodeUIntLE 2 bytes
  let (noNotAffectedOrders, bytes) ← decodeUIntLE 2 bytes
  let (partyIdEnteringFirm, bytes) ← decodeUInt 1 bytes
  let (massActionReason, bytes) ← decodeUInt 1 bytes
  let (pad2v2, bytes) ← Alpha.decode 2 bytes
  let (affectedOrdGrpComp_, bytes) ← decodeMany AffectedOrdGrpComp.decode noAffectedOrders.toNat bytes
  let (notAffectedOrdersGrpComp_, bytes) ← decodeMany NotAffectedOrdersGrpComp.decode noNotAffectedOrders.toNat bytes
  if fits_affectedOrdGrpComp : affectedOrdGrpComp_.length < 256 ^ 2 then
    if fits_notAffectedOrdersGrpComp : notAffectedOrdersGrpComp_.length < 256 ^ 2 then
      pure ({ pad2, rbcHeaderMeComp, massActionReportId, marketSegmentId, partyIdEnteringTrader, partyIdEnteringFirm, massActionReason, pad2v2, affectedOrdGrpComp := ⟨affectedOrdGrpComp_, fits_affectedOrdGrpComp⟩, notAffectedOrdersGrpComp := ⟨notAffectedOrdersGrpComp_, fits_notAffectedOrdersGrpComp⟩ }, bytes)
    else none
  else none

theorem encode_length_pos (message : SpecialistDeleteAllOrderBroadcast) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SpecialistDeleteAllOrderBroadcast) : (encode message).length ≤ 2097202 := by
  have bound_affectedOrdGrpComp := message.affectedOrdGrpComp.length_lt
  have bound_notAffectedOrdersGrpComp := message.notAffectedOrdersGrpComp.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, RbcHeaderMeComp.encode_length, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const AffectedOrdGrpComp.encode 16 AffectedOrdGrpComp.encode_length, encodeMany_length_const NotAffectedOrdersGrpComp.encode 16 NotAffectedOrdersGrpComp.encode_length]
  omega

@[simp] theorem decode_encode (message : SpecialistDeleteAllOrderBroadcast) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RbcHeaderMeComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
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
  rw [List.append_assoc, decodeMany_bounded 2 AffectedOrdGrpComp.encode AffectedOrdGrpComp.decode AffectedOrdGrpComp.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 NotAffectedOrdersGrpComp.encode NotAffectedOrdersGrpComp.decode NotAffectedOrdersGrpComp.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.affectedOrdGrpComp.length_lt, dite_eq_left message.notAffectedOrdersGrpComp.length_lt]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : SpecialistDeleteAllOrderBroadcast) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end SpecialistDeleteAllOrderBroadcast

/-- Specialist Instrument Event Notification: 82 bytes -/
structure SpecialistInstrumentEventNotification where
  pad2 : Alpha 2
  rbcHeaderMeComp : RbcHeaderMeComp
  securityId : BitVec 64
  transactTime : BitVec 64
  marketSegmentId : BitVec 32
  eventType : BitVec 8
  pad3 : Alpha 3
  deriving DecidableEq, Repr

namespace SpecialistInstrumentEventNotification

def encode (message : SpecialistInstrumentEventNotification) : List UInt8 :=
  Alpha.encode message.pad2
    ++ (RbcHeaderMeComp.encode message.rbcHeaderMeComp
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUInt 1 message.eventType
    ++ (Alpha.encode message.pad3))))))

def decode (bytes : List UInt8) : Option (SpecialistInstrumentEventNotification × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderMeComp, bytes) ← RbcHeaderMeComp.decode bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (eventType, bytes) ← decodeUInt 1 bytes
  let (pad3, bytes) ← Alpha.decode 3 bytes
  pure ({ pad2, rbcHeaderMeComp, securityId, transactTime, marketSegmentId, eventType, pad3 }, bytes)

@[simp] theorem encode_length (message : SpecialistInstrumentEventNotification) : (encode message).length = 82 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RbcHeaderMeComp.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : SpecialistInstrumentEventNotification) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SpecialistInstrumentEventNotification) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RbcHeaderMeComp.decode_encode, some_bind]
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

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : SpecialistInstrumentEventNotification) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end SpecialistInstrumentEventNotification

/-- Specialist Order Book Notification -/
structure SpecialistOrderBookNotification where
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
  quoteId : BitVec 64
  marketSegmentId : BitVec 32
  orderIdSfx : BitVec 32
  expireDate : BitVec 32
  partyIdExecutingUnit : BitVec 32
  partyIdSessionId : BitVec 32
  partyIdExecutingTrader : BitVec 32
  partyIdEnteringTrader : BitVec 32
  pad1 : Alpha 1
  execRestatementReason : BitVec 16
  partyIdEnteringFirm : BitVec 8
  ordStatus : OrdStatus
  execType : ExecType
  orderEventType : BitVec 8
  matchType : BitVec 8
  side : BitVec 8
  ordType : BitVec 8
  tradingCapacity : BitVec 8
  timeInForce : BitVec 8
  execInst : BitVec 8
  tradingSessionSubId : BitVec 8
  applSeqIndicator : BitVec 8
  triggered : BitVec 8
  orderAttributeLiquidityProvision : BitVec 8
  partyEnteringFirm : Alpha 5
  partyEnteringTrader : Alpha 6
  partyExecutingFirm : Alpha 5
  partyExecutingTrader : Alpha 6
  fixClOrdId : Alpha 20
  fillsGrpComp : Bounded 1 FillsGrpComp
  deriving DecidableEq, Repr

namespace SpecialistOrderBookNotification

def encode (message : SpecialistOrderBookNotification) : List UInt8 :=
  Alpha.encode message.pad2
    ++ (RbcHeaderMeComp.encode message.rbcHeaderMeComp
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 8 message.origClOrdId
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.execId
    ++ (encodeUIntLE 8 message.trdRegTsEntryTime
    ++ (encodeUIntLE 8 message.trdRegTsTimePriority
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 8 message.leavesQty
    ++ (encodeUIntLE 8 message.cumQty
    ++ (encodeUIntLE 8 message.cxlQty
    ++ (encodeUIntLE 8 message.orderQty
    ++ (encodeUIntLE 8 message.stopPx
    ++ (encodeUIntLE 8 message.quoteId
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.orderIdSfx
    ++ (encodeUIntLE 4 message.expireDate
    ++ (encodeUIntLE 4 message.partyIdExecutingUnit
    ++ (encodeUIntLE 4 message.partyIdSessionId
    ++ (encodeUIntLE 4 message.partyIdExecutingTrader
    ++ (encodeUIntLE 4 message.partyIdEnteringTrader
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.fillsGrpComp.val.length)
    ++ (Alpha.encode message.pad1
    ++ (encodeUIntLE 2 message.execRestatementReason
    ++ (encodeUInt 1 message.partyIdEnteringFirm
    ++ (OrdStatus.encode message.ordStatus
    ++ (ExecType.encode message.execType
    ++ (encodeUInt 1 message.orderEventType
    ++ (encodeUInt 1 message.matchType
    ++ (encodeUInt 1 message.side
    ++ (encodeUInt 1 message.ordType
    ++ (encodeUInt 1 message.tradingCapacity
    ++ (encodeUInt 1 message.timeInForce
    ++ (encodeUInt 1 message.execInst
    ++ (encodeUInt 1 message.tradingSessionSubId
    ++ (encodeUInt 1 message.applSeqIndicator
    ++ (encodeUInt 1 message.triggered
    ++ (encodeUInt 1 message.orderAttributeLiquidityProvision
    ++ (Alpha.encode message.partyEnteringFirm
    ++ (Alpha.encode message.partyEnteringTrader
    ++ (Alpha.encode message.partyExecutingFirm
    ++ (Alpha.encode message.partyExecutingTrader
    ++ (Alpha.encode message.fixClOrdId
    ++ (encodeMany FillsGrpComp.encode message.fillsGrpComp.val)))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (SpecialistOrderBookNotification × List UInt8) := do
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
  let (quoteId, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (orderIdSfx, bytes) ← decodeUIntLE 4 bytes
  let (expireDate, bytes) ← decodeUIntLE 4 bytes
  let (partyIdExecutingUnit, bytes) ← decodeUIntLE 4 bytes
  let (partyIdSessionId, bytes) ← decodeUIntLE 4 bytes
  let (partyIdExecutingTrader, bytes) ← decodeUIntLE 4 bytes
  let (partyIdEnteringTrader, bytes) ← decodeUIntLE 4 bytes
  let (noFills, bytes) ← decodeUInt 1 bytes
  let (pad1, bytes) ← Alpha.decode 1 bytes
  let (execRestatementReason, bytes) ← decodeUIntLE 2 bytes
  let (partyIdEnteringFirm, bytes) ← decodeUInt 1 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (orderEventType, bytes) ← decodeUInt 1 bytes
  let (matchType, bytes) ← decodeUInt 1 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (ordType, bytes) ← decodeUInt 1 bytes
  let (tradingCapacity, bytes) ← decodeUInt 1 bytes
  let (timeInForce, bytes) ← decodeUInt 1 bytes
  let (execInst, bytes) ← decodeUInt 1 bytes
  let (tradingSessionSubId, bytes) ← decodeUInt 1 bytes
  let (applSeqIndicator, bytes) ← decodeUInt 1 bytes
  let (triggered, bytes) ← decodeUInt 1 bytes
  let (orderAttributeLiquidityProvision, bytes) ← decodeUInt 1 bytes
  let (partyEnteringFirm, bytes) ← Alpha.decode 5 bytes
  let (partyEnteringTrader, bytes) ← Alpha.decode 6 bytes
  let (partyExecutingFirm, bytes) ← Alpha.decode 5 bytes
  let (partyExecutingTrader, bytes) ← Alpha.decode 6 bytes
  let (fixClOrdId, bytes) ← Alpha.decode 20 bytes
  let (fillsGrpComp_, bytes) ← decodeMany FillsGrpComp.decode noFills.toNat bytes
  if fits_fillsGrpComp : fillsGrpComp_.length < 256 ^ 1 then
    pure ({ pad2, rbcHeaderMeComp, orderId, clOrdId, origClOrdId, securityId, execId, trdRegTsEntryTime, trdRegTsTimePriority, price, leavesQty, cumQty, cxlQty, orderQty, stopPx, quoteId, marketSegmentId, orderIdSfx, expireDate, partyIdExecutingUnit, partyIdSessionId, partyIdExecutingTrader, partyIdEnteringTrader, pad1, execRestatementReason, partyIdEnteringFirm, ordStatus, execType, orderEventType, matchType, side, ordType, tradingCapacity, timeInForce, execInst, tradingSessionSubId, applSeqIndicator, triggered, orderAttributeLiquidityProvision, partyEnteringFirm, partyEnteringTrader, partyExecutingFirm, partyExecutingTrader, fixClOrdId, fillsGrpComp := ⟨fillsGrpComp_, fits_fillsGrpComp⟩ }, bytes)
  else none

theorem encode_length_pos (message : SpecialistOrderBookNotification) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : SpecialistOrderBookNotification) : (encode message).length ≤ 8418 := by
  have bound_fillsGrpComp := message.fillsGrpComp.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, RbcHeaderMeComp.encode_length, encodeUIntLE_length, encodeUInt_length, OrdStatus.encode_length, ExecType.encode_length, encodeMany_length_const FillsGrpComp.encode 32 FillsGrpComp.encode_length]
  omega

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : SpecialistOrderBookNotification) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RbcHeaderMeComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, OrdStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExecType.decode_encode, some_bind]
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
  rw [decodeMany_bounded 1 FillsGrpComp.encode FillsGrpComp.decode FillsGrpComp.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.fillsGrpComp.length_lt]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : SpecialistOrderBookNotification) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end SpecialistOrderBookNotification

/-- Specialist Rfq Reply Notification: 130 bytes -/
structure SpecialistRfqReplyNotification where
  pad2 : Alpha 2
  rbcHeaderMeComp : RbcHeaderMeComp
  securityId : BitVec 64
  transactTime : BitVec 64
  quoteId : BitVec 64
  bidPx : BitVec 64
  bidSize : BitVec 64
  offerPx : BitVec 64
  offerSize : BitVec 64
  marketSegmentId : BitVec 32
  partyExecutingFirm : Alpha 5
  pad7 : Alpha 7
  deriving DecidableEq, Repr

namespace SpecialistRfqReplyNotification

def encode (message : SpecialistRfqReplyNotification) : List UInt8 :=
  Alpha.encode message.pad2
    ++ (RbcHeaderMeComp.encode message.rbcHeaderMeComp
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 8 message.quoteId
    ++ (encodeUIntLE 8 message.bidPx
    ++ (encodeUIntLE 8 message.bidSize
    ++ (encodeUIntLE 8 message.offerPx
    ++ (encodeUIntLE 8 message.offerSize
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (Alpha.encode message.partyExecutingFirm
    ++ (Alpha.encode message.pad7)))))))))))

def decode (bytes : List UInt8) : Option (SpecialistRfqReplyNotification × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderMeComp, bytes) ← RbcHeaderMeComp.decode bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (quoteId, bytes) ← decodeUIntLE 8 bytes
  let (bidPx, bytes) ← decodeUIntLE 8 bytes
  let (bidSize, bytes) ← decodeUIntLE 8 bytes
  let (offerPx, bytes) ← decodeUIntLE 8 bytes
  let (offerSize, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (partyExecutingFirm, bytes) ← Alpha.decode 5 bytes
  let (pad7, bytes) ← Alpha.decode 7 bytes
  pure ({ pad2, rbcHeaderMeComp, securityId, transactTime, quoteId, bidPx, bidSize, offerPx, offerSize, marketSegmentId, partyExecutingFirm, pad7 }, bytes)

@[simp] theorem encode_length (message : SpecialistRfqReplyNotification) : (encode message).length = 130 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RbcHeaderMeComp.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : SpecialistRfqReplyNotification) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SpecialistRfqReplyNotification) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RbcHeaderMeComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
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

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : SpecialistRfqReplyNotification) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end SpecialistRfqReplyNotification

/-- Specialist Rfq Reply Response: 58 bytes -/
structure SpecialistRfqReplyResponse where
  pad2 : Alpha 2
  nrResponseHeaderMeComp : NrResponseHeaderMeComp
  transactTime : BitVec 64
  deriving DecidableEq, Repr

namespace SpecialistRfqReplyResponse

def encode (message : SpecialistRfqReplyResponse) : List UInt8 :=
  Alpha.encode message.pad2
    ++ (NrResponseHeaderMeComp.encode message.nrResponseHeaderMeComp
    ++ (encodeUIntLE 8 message.transactTime))

def decode (bytes : List UInt8) : Option (SpecialistRfqReplyResponse × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (nrResponseHeaderMeComp, bytes) ← NrResponseHeaderMeComp.decode bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  pure ({ pad2, nrResponseHeaderMeComp, transactTime }, bytes)

@[simp] theorem encode_length (message : SpecialistRfqReplyResponse) : (encode message).length = 58 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, NrResponseHeaderMeComp.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : SpecialistRfqReplyResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SpecialistRfqReplyResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NrResponseHeaderMeComp.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : SpecialistRfqReplyResponse) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end SpecialistRfqReplyResponse

/-- Specialist Security State Change Response: 58 bytes -/
structure SpecialistSecurityStateChangeResponse where
  pad2 : Alpha 2
  nrResponseHeaderMeComp : NrResponseHeaderMeComp
  securityStatusReportId : BitVec 64
  deriving DecidableEq, Repr

namespace SpecialistSecurityStateChangeResponse

def encode (message : SpecialistSecurityStateChangeResponse) : List UInt8 :=
  Alpha.encode message.pad2
    ++ (NrResponseHeaderMeComp.encode message.nrResponseHeaderMeComp
    ++ (encodeUIntLE 8 message.securityStatusReportId))

def decode (bytes : List UInt8) : Option (SpecialistSecurityStateChangeResponse × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (nrResponseHeaderMeComp, bytes) ← NrResponseHeaderMeComp.decode bytes
  let (securityStatusReportId, bytes) ← decodeUIntLE 8 bytes
  pure ({ pad2, nrResponseHeaderMeComp, securityStatusReportId }, bytes)

@[simp] theorem encode_length (message : SpecialistSecurityStateChangeResponse) : (encode message).length = 58 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, NrResponseHeaderMeComp.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : SpecialistSecurityStateChangeResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SpecialistSecurityStateChangeResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NrResponseHeaderMeComp.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : SpecialistSecurityStateChangeResponse) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end SpecialistSecurityStateChangeResponse

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
    ++ (ResponseHeaderComp.encode message.responseHeaderComp
    ++ (encodeUIntLE 4 message.applSubId
    ++ (Alpha.encode message.pad4)))

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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ResponseHeaderComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : SubscribeResponse) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end SubscribeResponse

/-- Tes Approve Broadcast: 202 bytes -/
structure TesApproveBroadcast where
  pad2 : Alpha 2
  rbcHeaderComp : RbcHeaderComp
  securityId : BitVec 64
  lastPx : BitVec 64
  allocQty : BitVec 64
  transactTime : BitVec 64
  transBkdTime : BitVec 64
  settlCurrFxRate : BitVec 64
  marketSegmentId : BitVec 32
  packageId : BitVec 32
  tesExecId : BitVec 32
  allocId : BitVec 32
  settlDate : BitVec 32
  trdType : BitVec 16
  side : BitVec 8
  valueCheckTypeValue : BitVec 8
  valueCheckTypeQuantity : BitVec 8
  tradeReportType : BitVec 8
  tradingCapacity : BitVec 8
  tradeAllocStatus : BitVec 8
  messageEventSource : MessageEventSource
  tradeReportId : Alpha 20
  partyExecutingFirm : Alpha 5
  partyExecutingTrader : Alpha 6
  partyIdEnteringFirm : BitVec 8
  partyEnteringTrader : Alpha 6
  rootPartyExecutingFirm : Alpha 5
  rootPartyExecutingTrader : Alpha 6
  freeText1 : Alpha 12
  freeText2 : Alpha 12
  freeText4 : Alpha 16
  pad2v2 : Alpha 2
  deriving DecidableEq, Repr

namespace TesApproveBroadcast

def encode (message : TesApproveBroadcast) : List UInt8 :=
  Alpha.encode message.pad2
    ++ (RbcHeaderComp.encode message.rbcHeaderComp
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.lastPx
    ++ (encodeUIntLE 8 message.allocQty
    ++ (encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 8 message.transBkdTime
    ++ (encodeUIntLE 8 message.settlCurrFxRate
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.packageId
    ++ (encodeUIntLE 4 message.tesExecId
    ++ (encodeUIntLE 4 message.allocId
    ++ (encodeUIntLE 4 message.settlDate
    ++ (encodeUIntLE 2 message.trdType
    ++ (encodeUInt 1 message.side
    ++ (encodeUInt 1 message.valueCheckTypeValue
    ++ (encodeUInt 1 message.valueCheckTypeQuantity
    ++ (encodeUInt 1 message.tradeReportType
    ++ (encodeUInt 1 message.tradingCapacity
    ++ (encodeUInt 1 message.tradeAllocStatus
    ++ (MessageEventSource.encode message.messageEventSource
    ++ (Alpha.encode message.tradeReportId
    ++ (Alpha.encode message.partyExecutingFirm
    ++ (Alpha.encode message.partyExecutingTrader
    ++ (encodeUInt 1 message.partyIdEnteringFirm
    ++ (Alpha.encode message.partyEnteringTrader
    ++ (Alpha.encode message.rootPartyExecutingFirm
    ++ (Alpha.encode message.rootPartyExecutingTrader
    ++ (Alpha.encode message.freeText1
    ++ (Alpha.encode message.freeText2
    ++ (Alpha.encode message.freeText4
    ++ (Alpha.encode message.pad2v2)))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (TesApproveBroadcast × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderComp, bytes) ← RbcHeaderComp.decode bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  let (allocQty, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (transBkdTime, bytes) ← decodeUIntLE 8 bytes
  let (settlCurrFxRate, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (packageId, bytes) ← decodeUIntLE 4 bytes
  let (tesExecId, bytes) ← decodeUIntLE 4 bytes
  let (allocId, bytes) ← decodeUIntLE 4 bytes
  let (settlDate, bytes) ← decodeUIntLE 4 bytes
  let (trdType, bytes) ← decodeUIntLE 2 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (valueCheckTypeValue, bytes) ← decodeUInt 1 bytes
  let (valueCheckTypeQuantity, bytes) ← decodeUInt 1 bytes
  let (tradeReportType, bytes) ← decodeUInt 1 bytes
  let (tradingCapacity, bytes) ← decodeUInt 1 bytes
  let (tradeAllocStatus, bytes) ← decodeUInt 1 bytes
  let (messageEventSource, bytes) ← MessageEventSource.decode bytes
  let (tradeReportId, bytes) ← Alpha.decode 20 bytes
  let (partyExecutingFirm, bytes) ← Alpha.decode 5 bytes
  let (partyExecutingTrader, bytes) ← Alpha.decode 6 bytes
  let (partyIdEnteringFirm, bytes) ← decodeUInt 1 bytes
  let (partyEnteringTrader, bytes) ← Alpha.decode 6 bytes
  let (rootPartyExecutingFirm, bytes) ← Alpha.decode 5 bytes
  let (rootPartyExecutingTrader, bytes) ← Alpha.decode 6 bytes
  let (freeText1, bytes) ← Alpha.decode 12 bytes
  let (freeText2, bytes) ← Alpha.decode 12 bytes
  let (freeText4, bytes) ← Alpha.decode 16 bytes
  let (pad2v2, bytes) ← Alpha.decode 2 bytes
  pure ({ pad2, rbcHeaderComp, securityId, lastPx, allocQty, transactTime, transBkdTime, settlCurrFxRate, marketSegmentId, packageId, tesExecId, allocId, settlDate, trdType, side, valueCheckTypeValue, valueCheckTypeQuantity, tradeReportType, tradingCapacity, tradeAllocStatus, messageEventSource, tradeReportId, partyExecutingFirm, partyExecutingTrader, partyIdEnteringFirm, partyEnteringTrader, rootPartyExecutingFirm, rootPartyExecutingTrader, freeText1, freeText2, freeText4, pad2v2 }, bytes)

@[simp] theorem encode_length (message : TesApproveBroadcast) : (encode message).length = 202 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RbcHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length, MessageEventSource.encode_length]

theorem encode_length_pos (message : TesApproveBroadcast) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : TesApproveBroadcast) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RbcHeaderComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
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
  rw [List.append_assoc, MessageEventSource.decode_encode, some_bind]
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

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : TesApproveBroadcast) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end TesApproveBroadcast

/-- Side Alloc Grp Bc Comp: 32 bytes -/
structure SideAllocGrpBcComp where
  allocQty : BitVec 64
  individualAllocId : BitVec 32
  partyExecutingFirm : Alpha 5
  partyExecutingTrader : Alpha 6
  side : BitVec 8
  tradeAllocStatus : BitVec 8
  pad7 : Alpha 7
  deriving DecidableEq, Repr

namespace SideAllocGrpBcComp

def encode (message : SideAllocGrpBcComp) : List UInt8 :=
  encodeUIntLE 8 message.allocQty
    ++ (encodeUIntLE 4 message.individualAllocId
    ++ (Alpha.encode message.partyExecutingFirm
    ++ (Alpha.encode message.partyExecutingTrader
    ++ (encodeUInt 1 message.side
    ++ (encodeUInt 1 message.tradeAllocStatus
    ++ (Alpha.encode message.pad7))))))

def decode (bytes : List UInt8) : Option (SideAllocGrpBcComp × List UInt8) := do
  let (allocQty, bytes) ← decodeUIntLE 8 bytes
  let (individualAllocId, bytes) ← decodeUIntLE 4 bytes
  let (partyExecutingFirm, bytes) ← Alpha.decode 5 bytes
  let (partyExecutingTrader, bytes) ← Alpha.decode 6 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (tradeAllocStatus, bytes) ← decodeUInt 1 bytes
  let (pad7, bytes) ← Alpha.decode 7 bytes
  pure ({ allocQty, individualAllocId, partyExecutingFirm, partyExecutingTrader, side, tradeAllocStatus, pad7 }, bytes)

@[simp] theorem encode_length (message : SideAllocGrpBcComp) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length]

theorem encode_length_pos (message : SideAllocGrpBcComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SideAllocGrpBcComp) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SideAllocGrpBcComp

/-- Tes Broadcast -/
structure TesBroadcast where
  pad2 : Alpha 2
  rbcHeaderComp : RbcHeaderComp
  securityId : BitVec 64
  lastPx : BitVec 64
  transactTime : BitVec 64
  transBkdTime : BitVec 64
  settlCurrFxRate : BitVec 64
  marketSegmentId : BitVec 32
  packageId : BitVec 32
  tesExecId : BitVec 32
  settlDate : BitVec 32
  trdType : BitVec 16
  tradeReportType : BitVec 8
  messageEventSource : MessageEventSource
  tradeReportText : Alpha 20
  tradeReportId : Alpha 20
  rootPartyExecutingFirm : Alpha 5
  rootPartyExecutingTrader : Alpha 6
  sideAllocGrpBcComp : Bounded 1 SideAllocGrpBcComp
  deriving DecidableEq, Repr

namespace TesBroadcast

def encode (message : TesBroadcast) : List UInt8 :=
  Alpha.encode message.pad2
    ++ (RbcHeaderComp.encode message.rbcHeaderComp
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.lastPx
    ++ (encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 8 message.transBkdTime
    ++ (encodeUIntLE 8 message.settlCurrFxRate
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.packageId
    ++ (encodeUIntLE 4 message.tesExecId
    ++ (encodeUIntLE 4 message.settlDate
    ++ (encodeUIntLE 2 message.trdType
    ++ (encodeUInt 1 message.tradeReportType
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.sideAllocGrpBcComp.val.length)
    ++ (MessageEventSource.encode message.messageEventSource
    ++ (Alpha.encode message.tradeReportText
    ++ (Alpha.encode message.tradeReportId
    ++ (Alpha.encode message.rootPartyExecutingFirm
    ++ (Alpha.encode message.rootPartyExecutingTrader
    ++ (encodeMany SideAllocGrpBcComp.encode message.sideAllocGrpBcComp.val)))))))))))))))))))

def decode (bytes : List UInt8) : Option (TesBroadcast × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderComp, bytes) ← RbcHeaderComp.decode bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (transBkdTime, bytes) ← decodeUIntLE 8 bytes
  let (settlCurrFxRate, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (packageId, bytes) ← decodeUIntLE 4 bytes
  let (tesExecId, bytes) ← decodeUIntLE 4 bytes
  let (settlDate, bytes) ← decodeUIntLE 4 bytes
  let (trdType, bytes) ← decodeUIntLE 2 bytes
  let (tradeReportType, bytes) ← decodeUInt 1 bytes
  let (noSideAllocs, bytes) ← decodeUInt 1 bytes
  let (messageEventSource, bytes) ← MessageEventSource.decode bytes
  let (tradeReportText, bytes) ← Alpha.decode 20 bytes
  let (tradeReportId, bytes) ← Alpha.decode 20 bytes
  let (rootPartyExecutingFirm, bytes) ← Alpha.decode 5 bytes
  let (rootPartyExecutingTrader, bytes) ← Alpha.decode 6 bytes
  let (sideAllocGrpBcComp_, bytes) ← decodeMany SideAllocGrpBcComp.decode noSideAllocs.toNat bytes
  if fits_sideAllocGrpBcComp : sideAllocGrpBcComp_.length < 256 ^ 1 then
    pure ({ pad2, rbcHeaderComp, securityId, lastPx, transactTime, transBkdTime, settlCurrFxRate, marketSegmentId, packageId, tesExecId, settlDate, trdType, tradeReportType, messageEventSource, tradeReportText, tradeReportId, rootPartyExecutingFirm, rootPartyExecutingTrader, sideAllocGrpBcComp := ⟨sideAllocGrpBcComp_, fits_sideAllocGrpBcComp⟩ }, bytes)
  else none

theorem encode_length_pos (message : TesBroadcast) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : TesBroadcast) : (encode message).length ≤ 8306 := by
  have bound_sideAllocGrpBcComp := message.sideAllocGrpBcComp.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, RbcHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length, MessageEventSource.encode_length, encodeMany_length_const SideAllocGrpBcComp.encode 32 SideAllocGrpBcComp.encode_length]
  omega

@[simp] theorem decode_encode (message : TesBroadcast) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RbcHeaderComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
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
  rw [List.append_assoc, MessageEventSource.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 SideAllocGrpBcComp.encode SideAllocGrpBcComp.decode SideAllocGrpBcComp.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.sideAllocGrpBcComp.length_lt]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : TesBroadcast) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

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
  messageEventSource : MessageEventSource
  tradeReportId : Alpha 20
  pad3 : Alpha 3
  deriving DecidableEq, Repr

namespace TesDeleteBroadcast

def encode (message : TesDeleteBroadcast) : List UInt8 :=
  Alpha.encode message.pad2
    ++ (RbcHeaderComp.encode message.rbcHeaderComp
    ++ (encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.packageId
    ++ (encodeUIntLE 4 message.tesExecId
    ++ (encodeUIntLE 2 message.trdType
    ++ (encodeUInt 1 message.deleteReason
    ++ (encodeUInt 1 message.tradeReportType
    ++ (MessageEventSource.encode message.messageEventSource
    ++ (Alpha.encode message.tradeReportId
    ++ (Alpha.encode message.pad3)))))))))))

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
  let (messageEventSource, bytes) ← MessageEventSource.decode bytes
  let (tradeReportId, bytes) ← Alpha.decode 20 bytes
  let (pad3, bytes) ← Alpha.decode 3 bytes
  pure ({ pad2, rbcHeaderComp, transactTime, marketSegmentId, packageId, tesExecId, trdType, deleteReason, tradeReportType, messageEventSource, tradeReportId, pad3 }, bytes)

@[simp] theorem encode_length (message : TesDeleteBroadcast) : (encode message).length = 82 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RbcHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length, MessageEventSource.encode_length]

theorem encode_length_pos (message : TesDeleteBroadcast) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TesDeleteBroadcast) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RbcHeaderComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
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
  rw [List.append_assoc, MessageEventSource.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : TesDeleteBroadcast) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

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
  messageEventSource : MessageEventSource
  pad3 : Alpha 3
  deriving DecidableEq, Repr

namespace TesExecutionBroadcast

def encode (message : TesExecutionBroadcast) : List UInt8 :=
  Alpha.encode message.pad2
    ++ (RbcHeaderComp.encode message.rbcHeaderComp
    ++ (encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.packageId
    ++ (encodeUIntLE 4 message.tesExecId
    ++ (encodeUIntLE 4 message.allocId
    ++ (encodeUIntLE 2 message.trdType
    ++ (encodeUInt 1 message.tradeReportType
    ++ (encodeUInt 1 message.side
    ++ (MessageEventSource.encode message.messageEventSource
    ++ (Alpha.encode message.pad3)))))))))))

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
  let (messageEventSource, bytes) ← MessageEventSource.decode bytes
  let (pad3, bytes) ← Alpha.decode 3 bytes
  pure ({ pad2, rbcHeaderComp, transactTime, marketSegmentId, packageId, tesExecId, allocId, trdType, tradeReportType, side, messageEventSource, pad3 }, bytes)

@[simp] theorem encode_length (message : TesExecutionBroadcast) : (encode message).length = 66 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RbcHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length, MessageEventSource.encode_length]

theorem encode_length_pos (message : TesExecutionBroadcast) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TesExecutionBroadcast) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RbcHeaderComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
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
  rw [List.append_assoc, MessageEventSource.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : TesExecutionBroadcast) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

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
    ++ (ResponseHeaderComp.encode message.responseHeaderComp
    ++ (encodeUIntLE 4 message.tesExecId
    ++ (Alpha.encode message.tradeReportId)))

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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ResponseHeaderComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : TesResponse) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end TesResponse

/-- Tes Trade Broadcast: 434 bytes -/
structure TesTradeBroadcast where
  pad2 : Alpha 2
  rbcHeaderComp : RbcHeaderComp
  securityId : BitVec 64
  lastPx : BitVec 64
  lastQty : BitVec 64
  transactTime : BitVec 64
  settlCurrAmt : BitVec 64
  sideGrossTradeAmt : BitVec 64
  settlCurrFxRate : BitVec 64
  accruedInteresAmt : BitVec 64
  couponRate : BitVec 64
  rootPartyIdClientId : BitVec 64
  executingTrader : BitVec 64
  rootPartyIdInvestmentDecisionMaker : BitVec 64
  packageId : BitVec 32
  marketSegmentId : BitVec 32
  tradeId : BitVec 32
  tradeDate : BitVec 32
  sideTradeId : BitVec 32
  rootPartyIdSessionId : BitVec 32
  rootPartyIdSettlementUnit : BitVec 32
  rootPartyIdContraUnit : BitVec 32
  rootPartyIdContraSettlementUnit : BitVec 32
  origTradeId : BitVec 32
  rootPartyIdExecutingUnit : BitVec 32
  rootPartyIdExecutingTrader : BitVec 32
  rootPartyIdClearingUnit : BitVec 32
  settlDate : BitVec 32
  numDaysInterest : BitVec 32
  negotiationId : BitVec 32
  srqsRelatedTradeId : BitVec 32
  trdType : BitVec 16
  lastMkt : BitVec 16
  side : BitVec 8
  tradingCapacity : BitVec 8
  tradeReportType : BitVec 8
  transferReason : BitVec 8
  tradePublishIndicator : BitVec 8
  deliveryType : BitVec 8
  lastCouponDeviationIndicator : BitVec 8
  refinancingEligibilityIndicator : BitVec 8
  clearingInstruction : BitVec 8
  orderAttributeLiquidityProvision : BitVec 8
  executingTraderQualifier : BitVec 8
  rootPartyIdInvestmentDecisionMakerQualifier : BitVec 8
  account : Alpha 2
  freeText1 : Alpha 12
  freeText2 : Alpha 12
  freeText4 : Alpha 16
  settlCurrency : Alpha 3
  rootPartyExecutingFirm : Alpha 5
  rootPartyExecutingTrader : Alpha 6
  rootPartyClearingFirm : Alpha 5
  rootPartyExecutingFirmKvNumber : Alpha 4
  rootPartySettlementAccount : Alpha 35
  rootPartySettlementLocation : Alpha 3
  rootPartySettlementFirm : Alpha 5
  rootPartyContraFirm : Alpha 5
  rootPartyContraSettlementFirm : Alpha 5
  rootPartyContraFirmKvNumber : Alpha 4
  rootPartyContraSettlementAccount : Alpha 35
  rootPartyContraSettlementLocation : Alpha 3
  rootPartyIdExecutionVenue : Alpha 4
  regulatoryTradeId : Alpha 52
  pad4 : Alpha 4
  deriving DecidableEq, Repr

namespace TesTradeBroadcast

def encode (message : TesTradeBroadcast) : List UInt8 :=
  Alpha.encode message.pad2
    ++ (RbcHeaderComp.encode message.rbcHeaderComp
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.lastPx
    ++ (encodeUIntLE 8 message.lastQty
    ++ (encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 8 message.settlCurrAmt
    ++ (encodeUIntLE 8 message.sideGrossTradeAmt
    ++ (encodeUIntLE 8 message.settlCurrFxRate
    ++ (encodeUIntLE 8 message.accruedInteresAmt
    ++ (encodeUIntLE 8 message.couponRate
    ++ (encodeUIntLE 8 message.rootPartyIdClientId
    ++ (encodeUIntLE 8 message.executingTrader
    ++ (encodeUIntLE 8 message.rootPartyIdInvestmentDecisionMaker
    ++ (encodeUIntLE 4 message.packageId
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.tradeId
    ++ (encodeUIntLE 4 message.tradeDate
    ++ (encodeUIntLE 4 message.sideTradeId
    ++ (encodeUIntLE 4 message.rootPartyIdSessionId
    ++ (encodeUIntLE 4 message.rootPartyIdSettlementUnit
    ++ (encodeUIntLE 4 message.rootPartyIdContraUnit
    ++ (encodeUIntLE 4 message.rootPartyIdContraSettlementUnit
    ++ (encodeUIntLE 4 message.origTradeId
    ++ (encodeUIntLE 4 message.rootPartyIdExecutingUnit
    ++ (encodeUIntLE 4 message.rootPartyIdExecutingTrader
    ++ (encodeUIntLE 4 message.rootPartyIdClearingUnit
    ++ (encodeUIntLE 4 message.settlDate
    ++ (encodeUIntLE 4 message.numDaysInterest
    ++ (encodeUIntLE 4 message.negotiationId
    ++ (encodeUIntLE 4 message.srqsRelatedTradeId
    ++ (encodeUIntLE 2 message.trdType
    ++ (encodeUIntLE 2 message.lastMkt
    ++ (encodeUInt 1 message.side
    ++ (encodeUInt 1 message.tradingCapacity
    ++ (encodeUInt 1 message.tradeReportType
    ++ (encodeUInt 1 message.transferReason
    ++ (encodeUInt 1 message.tradePublishIndicator
    ++ (encodeUInt 1 message.deliveryType
    ++ (encodeUInt 1 message.lastCouponDeviationIndicator
    ++ (encodeUInt 1 message.refinancingEligibilityIndicator
    ++ (encodeUInt 1 message.clearingInstruction
    ++ (encodeUInt 1 message.orderAttributeLiquidityProvision
    ++ (encodeUInt 1 message.executingTraderQualifier
    ++ (encodeUInt 1 message.rootPartyIdInvestmentDecisionMakerQualifier
    ++ (Alpha.encode message.account
    ++ (Alpha.encode message.freeText1
    ++ (Alpha.encode message.freeText2
    ++ (Alpha.encode message.freeText4
    ++ (Alpha.encode message.settlCurrency
    ++ (Alpha.encode message.rootPartyExecutingFirm
    ++ (Alpha.encode message.rootPartyExecutingTrader
    ++ (Alpha.encode message.rootPartyClearingFirm
    ++ (Alpha.encode message.rootPartyExecutingFirmKvNumber
    ++ (Alpha.encode message.rootPartySettlementAccount
    ++ (Alpha.encode message.rootPartySettlementLocation
    ++ (Alpha.encode message.rootPartySettlementFirm
    ++ (Alpha.encode message.rootPartyContraFirm
    ++ (Alpha.encode message.rootPartyContraSettlementFirm
    ++ (Alpha.encode message.rootPartyContraFirmKvNumber
    ++ (Alpha.encode message.rootPartyContraSettlementAccount
    ++ (Alpha.encode message.rootPartyContraSettlementLocation
    ++ (Alpha.encode message.rootPartyIdExecutionVenue
    ++ (Alpha.encode message.regulatoryTradeId
    ++ (Alpha.encode message.pad4))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (TesTradeBroadcast × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderComp, bytes) ← RbcHeaderComp.decode bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  let (lastQty, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (settlCurrAmt, bytes) ← decodeUIntLE 8 bytes
  let (sideGrossTradeAmt, bytes) ← decodeUIntLE 8 bytes
  let (settlCurrFxRate, bytes) ← decodeUIntLE 8 bytes
  let (accruedInteresAmt, bytes) ← decodeUIntLE 8 bytes
  let (couponRate, bytes) ← decodeUIntLE 8 bytes
  let (rootPartyIdClientId, bytes) ← decodeUIntLE 8 bytes
  let (executingTrader, bytes) ← decodeUIntLE 8 bytes
  let (rootPartyIdInvestmentDecisionMaker, bytes) ← decodeUIntLE 8 bytes
  let (packageId, bytes) ← decodeUIntLE 4 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (tradeId, bytes) ← decodeUIntLE 4 bytes
  let (tradeDate, bytes) ← decodeUIntLE 4 bytes
  let (sideTradeId, bytes) ← decodeUIntLE 4 bytes
  let (rootPartyIdSessionId, bytes) ← decodeUIntLE 4 bytes
  let (rootPartyIdSettlementUnit, bytes) ← decodeUIntLE 4 bytes
  let (rootPartyIdContraUnit, bytes) ← decodeUIntLE 4 bytes
  let (rootPartyIdContraSettlementUnit, bytes) ← decodeUIntLE 4 bytes
  let (origTradeId, bytes) ← decodeUIntLE 4 bytes
  let (rootPartyIdExecutingUnit, bytes) ← decodeUIntLE 4 bytes
  let (rootPartyIdExecutingTrader, bytes) ← decodeUIntLE 4 bytes
  let (rootPartyIdClearingUnit, bytes) ← decodeUIntLE 4 bytes
  let (settlDate, bytes) ← decodeUIntLE 4 bytes
  let (numDaysInterest, bytes) ← decodeUIntLE 4 bytes
  let (negotiationId, bytes) ← decodeUIntLE 4 bytes
  let (srqsRelatedTradeId, bytes) ← decodeUIntLE 4 bytes
  let (trdType, bytes) ← decodeUIntLE 2 bytes
  let (lastMkt, bytes) ← decodeUIntLE 2 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (tradingCapacity, bytes) ← decodeUInt 1 bytes
  let (tradeReportType, bytes) ← decodeUInt 1 bytes
  let (transferReason, bytes) ← decodeUInt 1 bytes
  let (tradePublishIndicator, bytes) ← decodeUInt 1 bytes
  let (deliveryType, bytes) ← decodeUInt 1 bytes
  let (lastCouponDeviationIndicator, bytes) ← decodeUInt 1 bytes
  let (refinancingEligibilityIndicator, bytes) ← decodeUInt 1 bytes
  let (clearingInstruction, bytes) ← decodeUInt 1 bytes
  let (orderAttributeLiquidityProvision, bytes) ← decodeUInt 1 bytes
  let (executingTraderQualifier, bytes) ← decodeUInt 1 bytes
  let (rootPartyIdInvestmentDecisionMakerQualifier, bytes) ← decodeUInt 1 bytes
  let (account, bytes) ← Alpha.decode 2 bytes
  let (freeText1, bytes) ← Alpha.decode 12 bytes
  let (freeText2, bytes) ← Alpha.decode 12 bytes
  let (freeText4, bytes) ← Alpha.decode 16 bytes
  let (settlCurrency, bytes) ← Alpha.decode 3 bytes
  let (rootPartyExecutingFirm, bytes) ← Alpha.decode 5 bytes
  let (rootPartyExecutingTrader, bytes) ← Alpha.decode 6 bytes
  let (rootPartyClearingFirm, bytes) ← Alpha.decode 5 bytes
  let (rootPartyExecutingFirmKvNumber, bytes) ← Alpha.decode 4 bytes
  let (rootPartySettlementAccount, bytes) ← Alpha.decode 35 bytes
  let (rootPartySettlementLocation, bytes) ← Alpha.decode 3 bytes
  let (rootPartySettlementFirm, bytes) ← Alpha.decode 5 bytes
  let (rootPartyContraFirm, bytes) ← Alpha.decode 5 bytes
  let (rootPartyContraSettlementFirm, bytes) ← Alpha.decode 5 bytes
  let (rootPartyContraFirmKvNumber, bytes) ← Alpha.decode 4 bytes
  let (rootPartyContraSettlementAccount, bytes) ← Alpha.decode 35 bytes
  let (rootPartyContraSettlementLocation, bytes) ← Alpha.decode 3 bytes
  let (rootPartyIdExecutionVenue, bytes) ← Alpha.decode 4 bytes
  let (regulatoryTradeId, bytes) ← Alpha.decode 52 bytes
  let (pad4, bytes) ← Alpha.decode 4 bytes
  pure ({ pad2, rbcHeaderComp, securityId, lastPx, lastQty, transactTime, settlCurrAmt, sideGrossTradeAmt, settlCurrFxRate, accruedInteresAmt, couponRate, rootPartyIdClientId, executingTrader, rootPartyIdInvestmentDecisionMaker, packageId, marketSegmentId, tradeId, tradeDate, sideTradeId, rootPartyIdSessionId, rootPartyIdSettlementUnit, rootPartyIdContraUnit, rootPartyIdContraSettlementUnit, origTradeId, rootPartyIdExecutingUnit, rootPartyIdExecutingTrader, rootPartyIdClearingUnit, settlDate, numDaysInterest, negotiationId, srqsRelatedTradeId, trdType, lastMkt, side, tradingCapacity, tradeReportType, transferReason, tradePublishIndicator, deliveryType, lastCouponDeviationIndicator, refinancingEligibilityIndicator, clearingInstruction, orderAttributeLiquidityProvision, executingTraderQualifier, rootPartyIdInvestmentDecisionMakerQualifier, account, freeText1, freeText2, freeText4, settlCurrency, rootPartyExecutingFirm, rootPartyExecutingTrader, rootPartyClearingFirm, rootPartyExecutingFirmKvNumber, rootPartySettlementAccount, rootPartySettlementLocation, rootPartySettlementFirm, rootPartyContraFirm, rootPartyContraSettlementFirm, rootPartyContraFirmKvNumber, rootPartyContraSettlementAccount, rootPartyContraSettlementLocation, rootPartyIdExecutionVenue, regulatoryTradeId, pad4 }, bytes)

@[simp] theorem encode_length (message : TesTradeBroadcast) : (encode message).length = 434 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RbcHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : TesTradeBroadcast) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : TesTradeBroadcast) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RbcHeaderComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
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

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : TesTradeBroadcast) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

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
    ++ (RbcHeaderComp.encode message.rbcHeaderComp
    ++ (encodeUIntLE 4 message.tradeDate
    ++ (encodeUInt 1 message.tradSesEvent
    ++ (Alpha.encode message.pad3))))

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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RbcHeaderComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : TesTradingSessionStatusBroadcast) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end TesTradingSessionStatusBroadcast

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
    ++ (RbcHeaderComp.encode message.rbcHeaderComp
    ++ (encodeUInt 1 message.tradSesEvent
    ++ (Alpha.encode message.pad7)))

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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RbcHeaderComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : TmTradingSessionStatusBroadcast) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

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
    ++ (NotifHeaderComp.encode message.notifHeaderComp
    ++ (encodeUIntLE 8 message.throttleTimeInterval
    ++ (encodeUIntLE 4 message.throttleNoMsgs
    ++ (encodeUIntLE 4 message.throttleDisconnectLimit))))

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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NotifHeaderComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : ThrottleUpdateNotification) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end ThrottleUpdateNotification

/-- Trade Broadcast: 498 bytes -/
structure TradeBroadcast where
  pad2 : Alpha 2
  rbcHeaderComp : RbcHeaderComp
  securityId : BitVec 64
  price : BitVec 64
  lastPx : BitVec 64
  lastQty : BitVec 64
  settlCurrAmt : BitVec 64
  settlCurrFxRate : BitVec 64
  transactTime : BitVec 64
  orderId : BitVec 64
  clOrdId : BitVec 64
  leavesQty : BitVec 64
  cumQty : BitVec 64
  sideGrossTradeAmt : BitVec 64
  accruedInteresAmt : BitVec 64
  couponRate : BitVec 64
  rootPartyIdClientId : BitVec 64
  executingTrader : BitVec 64
  rootPartyIdInvestmentDecisionMaker : BitVec 64
  tradeId : BitVec 32
  origTradeId : BitVec 32
  rootPartyIdExecutingUnit : BitVec 32
  rootPartyIdSessionId : BitVec 32
  rootPartyIdExecutingTrader : BitVec 32
  rootPartyIdSettlementUnit : BitVec 32
  rootPartyIdClearingUnit : BitVec 32
  rootPartyIdContraUnit : BitVec 32
  rootPartyIdContraSettlementUnit : BitVec 32
  partyIdSpecialistTrader : BitVec 32
  orderIdSfx : BitVec 32
  marketSegmentId : BitVec 32
  sideTradeId : BitVec 32
  sideTradeReportId : BitVec 32
  tradeNumber : BitVec 32
  matchDate : BitVec 32
  settlDate : BitVec 32
  trdMatchId : BitVec 32
  numDaysInterest : BitVec 32
  lastMkt : BitVec 16
  tradeReportType : BitVec 8
  transferReason : BitVec 8
  matchType : BitVec 8
  matchSubType : BitVec 8
  side : BitVec 8
  sideLiquidityInd : BitVec 8
  deliveryType : BitVec 8
  tradingCapacity : BitVec 8
  lastCouponDeviationIndicator : BitVec 8
  refinancingEligibilityIndicator : BitVec 8
  clearingInstruction : BitVec 8
  orderOrigination : BitVec 8
  orderAttributeLiquidityProvision : BitVec 8
  executingTraderQualifier : BitVec 8
  rootPartyIdInvestmentDecisionMakerQualifier : BitVec 8
  account : Alpha 2
  settlCurrency : Alpha 3
  currency : Alpha 3
  freeText1 : Alpha 12
  freeText2 : Alpha 12
  freeText4 : Alpha 16
  orderCategory : OrderCategory
  ordType : BitVec 8
  rootPartyExecutingFirm : Alpha 5
  rootPartyExecutingTrader : Alpha 6
  rootPartyClearingFirm : Alpha 5
  rootPartyExecutingFirmKvNumber : Alpha 4
  rootPartySettlementAccount : Alpha 35
  rootPartySettlementLocation : Alpha 3
  rootPartySettlementFirm : Alpha 5
  rootPartyContraFirm : Alpha 5
  rootPartyContraSettlementFirm : Alpha 5
  rootPartyContraFirmKvNumber : Alpha 4
  rootPartyContraSettlementAccount : Alpha 35
  rootPartyContraSettlementLocation : Alpha 3
  partySpecialistFirm : Alpha 5
  partySpecialistTrader : Alpha 6
  regulatoryTradeId : Alpha 52
  rootPartyIdExecutionVenue : Alpha 4
  pad3 : Alpha 3
  deriving DecidableEq, Repr

namespace TradeBroadcast

def encode (message : TradeBroadcast) : List UInt8 :=
  Alpha.encode message.pad2
    ++ (RbcHeaderComp.encode message.rbcHeaderComp
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 8 message.lastPx
    ++ (encodeUIntLE 8 message.lastQty
    ++ (encodeUIntLE 8 message.settlCurrAmt
    ++ (encodeUIntLE 8 message.settlCurrFxRate
    ++ (encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 8 message.leavesQty
    ++ (encodeUIntLE 8 message.cumQty
    ++ (encodeUIntLE 8 message.sideGrossTradeAmt
    ++ (encodeUIntLE 8 message.accruedInteresAmt
    ++ (encodeUIntLE 8 message.couponRate
    ++ (encodeUIntLE 8 message.rootPartyIdClientId
    ++ (encodeUIntLE 8 message.executingTrader
    ++ (encodeUIntLE 8 message.rootPartyIdInvestmentDecisionMaker
    ++ (encodeUIntLE 4 message.tradeId
    ++ (encodeUIntLE 4 message.origTradeId
    ++ (encodeUIntLE 4 message.rootPartyIdExecutingUnit
    ++ (encodeUIntLE 4 message.rootPartyIdSessionId
    ++ (encodeUIntLE 4 message.rootPartyIdExecutingTrader
    ++ (encodeUIntLE 4 message.rootPartyIdSettlementUnit
    ++ (encodeUIntLE 4 message.rootPartyIdClearingUnit
    ++ (encodeUIntLE 4 message.rootPartyIdContraUnit
    ++ (encodeUIntLE 4 message.rootPartyIdContraSettlementUnit
    ++ (encodeUIntLE 4 message.partyIdSpecialistTrader
    ++ (encodeUIntLE 4 message.orderIdSfx
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.sideTradeId
    ++ (encodeUIntLE 4 message.sideTradeReportId
    ++ (encodeUIntLE 4 message.tradeNumber
    ++ (encodeUIntLE 4 message.matchDate
    ++ (encodeUIntLE 4 message.settlDate
    ++ (encodeUIntLE 4 message.trdMatchId
    ++ (encodeUIntLE 4 message.numDaysInterest
    ++ (encodeUIntLE 2 message.lastMkt
    ++ (encodeUInt 1 message.tradeReportType
    ++ (encodeUInt 1 message.transferReason
    ++ (encodeUInt 1 message.matchType
    ++ (encodeUInt 1 message.matchSubType
    ++ (encodeUInt 1 message.side
    ++ (encodeUInt 1 message.sideLiquidityInd
    ++ (encodeUInt 1 message.deliveryType
    ++ (encodeUInt 1 message.tradingCapacity
    ++ (encodeUInt 1 message.lastCouponDeviationIndicator
    ++ (encodeUInt 1 message.refinancingEligibilityIndicator
    ++ (encodeUInt 1 message.clearingInstruction
    ++ (encodeUInt 1 message.orderOrigination
    ++ (encodeUInt 1 message.orderAttributeLiquidityProvision
    ++ (encodeUInt 1 message.executingTraderQualifier
    ++ (encodeUInt 1 message.rootPartyIdInvestmentDecisionMakerQualifier
    ++ (Alpha.encode message.account
    ++ (Alpha.encode message.settlCurrency
    ++ (Alpha.encode message.currency
    ++ (Alpha.encode message.freeText1
    ++ (Alpha.encode message.freeText2
    ++ (Alpha.encode message.freeText4
    ++ (OrderCategory.encode message.orderCategory
    ++ (encodeUInt 1 message.ordType
    ++ (Alpha.encode message.rootPartyExecutingFirm
    ++ (Alpha.encode message.rootPartyExecutingTrader
    ++ (Alpha.encode message.rootPartyClearingFirm
    ++ (Alpha.encode message.rootPartyExecutingFirmKvNumber
    ++ (Alpha.encode message.rootPartySettlementAccount
    ++ (Alpha.encode message.rootPartySettlementLocation
    ++ (Alpha.encode message.rootPartySettlementFirm
    ++ (Alpha.encode message.rootPartyContraFirm
    ++ (Alpha.encode message.rootPartyContraSettlementFirm
    ++ (Alpha.encode message.rootPartyContraFirmKvNumber
    ++ (Alpha.encode message.rootPartyContraSettlementAccount
    ++ (Alpha.encode message.rootPartyContraSettlementLocation
    ++ (Alpha.encode message.partySpecialistFirm
    ++ (Alpha.encode message.partySpecialistTrader
    ++ (Alpha.encode message.regulatoryTradeId
    ++ (Alpha.encode message.rootPartyIdExecutionVenue
    ++ (Alpha.encode message.pad3))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (TradeBroadcast × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderComp, bytes) ← RbcHeaderComp.decode bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  let (lastQty, bytes) ← decodeUIntLE 8 bytes
  let (settlCurrAmt, bytes) ← decodeUIntLE 8 bytes
  let (settlCurrFxRate, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (leavesQty, bytes) ← decodeUIntLE 8 bytes
  let (cumQty, bytes) ← decodeUIntLE 8 bytes
  let (sideGrossTradeAmt, bytes) ← decodeUIntLE 8 bytes
  let (accruedInteresAmt, bytes) ← decodeUIntLE 8 bytes
  let (couponRate, bytes) ← decodeUIntLE 8 bytes
  let (rootPartyIdClientId, bytes) ← decodeUIntLE 8 bytes
  let (executingTrader, bytes) ← decodeUIntLE 8 bytes
  let (rootPartyIdInvestmentDecisionMaker, bytes) ← decodeUIntLE 8 bytes
  let (tradeId, bytes) ← decodeUIntLE 4 bytes
  let (origTradeId, bytes) ← decodeUIntLE 4 bytes
  let (rootPartyIdExecutingUnit, bytes) ← decodeUIntLE 4 bytes
  let (rootPartyIdSessionId, bytes) ← decodeUIntLE 4 bytes
  let (rootPartyIdExecutingTrader, bytes) ← decodeUIntLE 4 bytes
  let (rootPartyIdSettlementUnit, bytes) ← decodeUIntLE 4 bytes
  let (rootPartyIdClearingUnit, bytes) ← decodeUIntLE 4 bytes
  let (rootPartyIdContraUnit, bytes) ← decodeUIntLE 4 bytes
  let (rootPartyIdContraSettlementUnit, bytes) ← decodeUIntLE 4 bytes
  let (partyIdSpecialistTrader, bytes) ← decodeUIntLE 4 bytes
  let (orderIdSfx, bytes) ← decodeUIntLE 4 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (sideTradeId, bytes) ← decodeUIntLE 4 bytes
  let (sideTradeReportId, bytes) ← decodeUIntLE 4 bytes
  let (tradeNumber, bytes) ← decodeUIntLE 4 bytes
  let (matchDate, bytes) ← decodeUIntLE 4 bytes
  let (settlDate, bytes) ← decodeUIntLE 4 bytes
  let (trdMatchId, bytes) ← decodeUIntLE 4 bytes
  let (numDaysInterest, bytes) ← decodeUIntLE 4 bytes
  let (lastMkt, bytes) ← decodeUIntLE 2 bytes
  let (tradeReportType, bytes) ← decodeUInt 1 bytes
  let (transferReason, bytes) ← decodeUInt 1 bytes
  let (matchType, bytes) ← decodeUInt 1 bytes
  let (matchSubType, bytes) ← decodeUInt 1 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (sideLiquidityInd, bytes) ← decodeUInt 1 bytes
  let (deliveryType, bytes) ← decodeUInt 1 bytes
  let (tradingCapacity, bytes) ← decodeUInt 1 bytes
  let (lastCouponDeviationIndicator, bytes) ← decodeUInt 1 bytes
  let (refinancingEligibilityIndicator, bytes) ← decodeUInt 1 bytes
  let (clearingInstruction, bytes) ← decodeUInt 1 bytes
  let (orderOrigination, bytes) ← decodeUInt 1 bytes
  let (orderAttributeLiquidityProvision, bytes) ← decodeUInt 1 bytes
  let (executingTraderQualifier, bytes) ← decodeUInt 1 bytes
  let (rootPartyIdInvestmentDecisionMakerQualifier, bytes) ← decodeUInt 1 bytes
  let (account, bytes) ← Alpha.decode 2 bytes
  let (settlCurrency, bytes) ← Alpha.decode 3 bytes
  let (currency, bytes) ← Alpha.decode 3 bytes
  let (freeText1, bytes) ← Alpha.decode 12 bytes
  let (freeText2, bytes) ← Alpha.decode 12 bytes
  let (freeText4, bytes) ← Alpha.decode 16 bytes
  let (orderCategory, bytes) ← OrderCategory.decode bytes
  let (ordType, bytes) ← decodeUInt 1 bytes
  let (rootPartyExecutingFirm, bytes) ← Alpha.decode 5 bytes
  let (rootPartyExecutingTrader, bytes) ← Alpha.decode 6 bytes
  let (rootPartyClearingFirm, bytes) ← Alpha.decode 5 bytes
  let (rootPartyExecutingFirmKvNumber, bytes) ← Alpha.decode 4 bytes
  let (rootPartySettlementAccount, bytes) ← Alpha.decode 35 bytes
  let (rootPartySettlementLocation, bytes) ← Alpha.decode 3 bytes
  let (rootPartySettlementFirm, bytes) ← Alpha.decode 5 bytes
  let (rootPartyContraFirm, bytes) ← Alpha.decode 5 bytes
  let (rootPartyContraSettlementFirm, bytes) ← Alpha.decode 5 bytes
  let (rootPartyContraFirmKvNumber, bytes) ← Alpha.decode 4 bytes
  let (rootPartyContraSettlementAccount, bytes) ← Alpha.decode 35 bytes
  let (rootPartyContraSettlementLocation, bytes) ← Alpha.decode 3 bytes
  let (partySpecialistFirm, bytes) ← Alpha.decode 5 bytes
  let (partySpecialistTrader, bytes) ← Alpha.decode 6 bytes
  let (regulatoryTradeId, bytes) ← Alpha.decode 52 bytes
  let (rootPartyIdExecutionVenue, bytes) ← Alpha.decode 4 bytes
  let (pad3, bytes) ← Alpha.decode 3 bytes
  pure ({ pad2, rbcHeaderComp, securityId, price, lastPx, lastQty, settlCurrAmt, settlCurrFxRate, transactTime, orderId, clOrdId, leavesQty, cumQty, sideGrossTradeAmt, accruedInteresAmt, couponRate, rootPartyIdClientId, executingTrader, rootPartyIdInvestmentDecisionMaker, tradeId, origTradeId, rootPartyIdExecutingUnit, rootPartyIdSessionId, rootPartyIdExecutingTrader, rootPartyIdSettlementUnit, rootPartyIdClearingUnit, rootPartyIdContraUnit, rootPartyIdContraSettlementUnit, partyIdSpecialistTrader, orderIdSfx, marketSegmentId, sideTradeId, sideTradeReportId, tradeNumber, matchDate, settlDate, trdMatchId, numDaysInterest, lastMkt, tradeReportType, transferReason, matchType, matchSubType, side, sideLiquidityInd, deliveryType, tradingCapacity, lastCouponDeviationIndicator, refinancingEligibilityIndicator, clearingInstruction, orderOrigination, orderAttributeLiquidityProvision, executingTraderQualifier, rootPartyIdInvestmentDecisionMakerQualifier, account, settlCurrency, currency, freeText1, freeText2, freeText4, orderCategory, ordType, rootPartyExecutingFirm, rootPartyExecutingTrader, rootPartyClearingFirm, rootPartyExecutingFirmKvNumber, rootPartySettlementAccount, rootPartySettlementLocation, rootPartySettlementFirm, rootPartyContraFirm, rootPartyContraSettlementFirm, rootPartyContraFirmKvNumber, rootPartyContraSettlementAccount, rootPartyContraSettlementLocation, partySpecialistFirm, partySpecialistTrader, regulatoryTradeId, rootPartyIdExecutionVenue, pad3 }, bytes)

@[simp] theorem encode_length (message : TradeBroadcast) : (encode message).length = 498 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RbcHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length, OrderCategory.encode_length]

theorem encode_length_pos (message : TradeBroadcast) : (encode message).length > 0 := by
  rw [encode_length]
  decide

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : TradeBroadcast) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RbcHeaderComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
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
  rw [List.append_assoc, OrderCategory.decode_encode, some_bind]
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

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : TradeBroadcast) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

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
    ++ (RbcHeaderMeComp.encode message.rbcHeaderMeComp
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.tradeDate
    ++ (encodeUInt 1 message.tradSesEvent
    ++ (Alpha.encode message.refApplLastMsgId
    ++ (Alpha.encode message.pad7))))))

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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RbcHeaderMeComp.decode_encode, some_bind]
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

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : TradingSessionStatusBroadcast) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end TradingSessionStatusBroadcast

/-- Trailing Stop Update Notification: 154 bytes -/
structure TrailingStopUpdateNotification where
  pad2 : Alpha 2
  rbcHeaderMeComp : RbcHeaderMeComp
  orderId : BitVec 64
  clOrdId : BitVec 64
  origClOrdId : BitVec 64
  securityId : BitVec 64
  execId : BitVec 64
  stopPx : BitVec 64
  orderQty : BitVec 64
  orderIdSfx : BitVec 32
  marketSegmentId : BitVec 32
  execRestatementReason : BitVec 16
  ordStatus : OrdStatus
  execType : ExecType
  side : BitVec 8
  fixClOrdId : Alpha 20
  pad7 : Alpha 7
  deriving DecidableEq, Repr

namespace TrailingStopUpdateNotification

def encode (message : TrailingStopUpdateNotification) : List UInt8 :=
  Alpha.encode message.pad2
    ++ (RbcHeaderMeComp.encode message.rbcHeaderMeComp
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 8 message.origClOrdId
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.execId
    ++ (encodeUIntLE 8 message.stopPx
    ++ (encodeUIntLE 8 message.orderQty
    ++ (encodeUIntLE 4 message.orderIdSfx
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 2 message.execRestatementReason
    ++ (OrdStatus.encode message.ordStatus
    ++ (ExecType.encode message.execType
    ++ (encodeUInt 1 message.side
    ++ (Alpha.encode message.fixClOrdId
    ++ (Alpha.encode message.pad7))))))))))))))))

def decode (bytes : List UInt8) : Option (TrailingStopUpdateNotification × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderMeComp, bytes) ← RbcHeaderMeComp.decode bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (origClOrdId, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  let (stopPx, bytes) ← decodeUIntLE 8 bytes
  let (orderQty, bytes) ← decodeUIntLE 8 bytes
  let (orderIdSfx, bytes) ← decodeUIntLE 4 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (execRestatementReason, bytes) ← decodeUIntLE 2 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (fixClOrdId, bytes) ← Alpha.decode 20 bytes
  let (pad7, bytes) ← Alpha.decode 7 bytes
  pure ({ pad2, rbcHeaderMeComp, orderId, clOrdId, origClOrdId, securityId, execId, stopPx, orderQty, orderIdSfx, marketSegmentId, execRestatementReason, ordStatus, execType, side, fixClOrdId, pad7 }, bytes)

@[simp] theorem encode_length (message : TrailingStopUpdateNotification) : (encode message).length = 154 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RbcHeaderMeComp.encode_length, encodeUIntLE_length, OrdStatus.encode_length, ExecType.encode_length, encodeUInt_length]

theorem encode_length_pos (message : TrailingStopUpdateNotification) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TrailingStopUpdateNotification) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RbcHeaderMeComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, OrdStatus.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ExecType.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : TrailingStopUpdateNotification) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end TrailingStopUpdateNotification

/-- Unsubscribe Response: 26 bytes -/
structure UnsubscribeResponse where
  pad2 : Alpha 2
  responseHeaderComp : ResponseHeaderComp
  deriving DecidableEq, Repr

namespace UnsubscribeResponse

def encode (message : UnsubscribeResponse) : List UInt8 :=
  Alpha.encode message.pad2
    ++ (ResponseHeaderComp.encode message.responseHeaderComp)

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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [ResponseHeaderComp.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : UnsubscribeResponse) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end UnsubscribeResponse

/-- User Login Response: 26 bytes -/
structure UserLoginResponse where
  pad2 : Alpha 2
  responseHeaderComp : ResponseHeaderComp
  deriving DecidableEq, Repr

namespace UserLoginResponse

def encode (message : UserLoginResponse) : List UInt8 :=
  Alpha.encode message.pad2
    ++ (ResponseHeaderComp.encode message.responseHeaderComp)

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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [ResponseHeaderComp.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : UserLoginResponse) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end UserLoginResponse

/-- User Logout Response: 26 bytes -/
structure UserLogoutResponse where
  pad2 : Alpha 2
  responseHeaderComp : ResponseHeaderComp
  deriving DecidableEq, Repr

namespace UserLogoutResponse

def encode (message : UserLogoutResponse) : List UInt8 :=
  Alpha.encode message.pad2
    ++ (ResponseHeaderComp.encode message.responseHeaderComp)

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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [ResponseHeaderComp.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : UserLogoutResponse) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end UserLogoutResponse

/-- Order Book Item Grp Comp: 40 bytes -/
structure OrderBookItemGrpComp where
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
  encodeUIntLE 8 message.bestBidPx
    ++ (encodeUIntLE 8 message.bestBidSize
    ++ (encodeUIntLE 8 message.bestOfferPx
    ++ (encodeUIntLE 8 message.bestOfferSize
    ++ (encodeUInt 1 message.mdBookType
    ++ (encodeUInt 1 message.mdSubBookType
    ++ (Alpha.encode message.pad6))))))

def decode (bytes : List UInt8) : Option (OrderBookItemGrpComp × List UInt8) := do
  let (bestBidPx, bytes) ← decodeUIntLE 8 bytes
  let (bestBidSize, bytes) ← decodeUIntLE 8 bytes
  let (bestOfferPx, bytes) ← decodeUIntLE 8 bytes
  let (bestOfferSize, bytes) ← decodeUIntLE 8 bytes
  let (mdBookType, bytes) ← decodeUInt 1 bytes
  let (mdSubBookType, bytes) ← decodeUInt 1 bytes
  let (pad6, bytes) ← Alpha.decode 6 bytes
  pure ({ bestBidPx, bestBidSize, bestOfferPx, bestOfferSize, mdBookType, mdSubBookType, pad6 }, bytes)

@[simp] theorem encode_length (message : OrderBookItemGrpComp) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : OrderBookItemGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderBookItemGrpComp) (rest : List UInt8) :
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

end OrderBookItemGrpComp

/-- Xetra En Light Create Deal Notification -/
structure XetraEnLightCreateDealNotification where
  pad2 : Alpha 2
  rbcHeaderComp : RbcHeaderComp
  transactTime : BitVec 64
  lastPx : BitVec 64
  lastQty : BitVec 64
  quoteId : BitVec 64
  securityId : BitVec 64
  partyIdClientId : BitVec 64
  partyIdInvestmentDecisionMaker : BitVec 64
  executingTrader : BitVec 64
  negotiationId : BitVec 32
  tradeId : BitVec 32
  settlDate : BitVec 32
  tradingCapacity : BitVec 8
  trdRptStatus : BitVec 8
  messageEventSource : MessageEventSource
  side : BitVec 8
  allocMethod : BitVec 8
  orderAttributeLiquidityProvision : BitVec 8
  executingTraderQualifier : BitVec 8
  partyIdInvestmentDecisionMakerQualifier : BitVec 8
  rootPartyExecutingFirm : Alpha 5
  rootPartyExecutingTrader : Alpha 6
  rootPartyEnteringTrader : Alpha 6
  targetPartyExecutingFirm : Alpha 5
  targetPartyExecutingTrader : Alpha 6
  firmTradeId : Alpha 20
  firmNegotiationId : Alpha 20
  freeText1 : Alpha 12
  freeText2 : Alpha 12
  freeText4 : Alpha 16
  pad7 : Alpha 7
  orderBookItemGrpComp : Bounded 1 OrderBookItemGrpComp
  deriving DecidableEq, Repr

namespace XetraEnLightCreateDealNotification

def encode (message : XetraEnLightCreateDealNotification) : List UInt8 :=
  Alpha.encode message.pad2
    ++ (RbcHeaderComp.encode message.rbcHeaderComp
    ++ (encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 8 message.lastPx
    ++ (encodeUIntLE 8 message.lastQty
    ++ (encodeUIntLE 8 message.quoteId
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.partyIdClientId
    ++ (encodeUIntLE 8 message.partyIdInvestmentDecisionMaker
    ++ (encodeUIntLE 8 message.executingTrader
    ++ (encodeUIntLE 4 message.negotiationId
    ++ (encodeUIntLE 4 message.tradeId
    ++ (encodeUIntLE 4 message.settlDate
    ++ (encodeUInt 1 message.tradingCapacity
    ++ (encodeUInt 1 message.trdRptStatus
    ++ (MessageEventSource.encode message.messageEventSource
    ++ (encodeUInt 1 message.side
    ++ (encodeUInt 1 message.allocMethod
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.orderBookItemGrpComp.val.length)
    ++ (encodeUInt 1 message.orderAttributeLiquidityProvision
    ++ (encodeUInt 1 message.executingTraderQualifier
    ++ (encodeUInt 1 message.partyIdInvestmentDecisionMakerQualifier
    ++ (Alpha.encode message.rootPartyExecutingFirm
    ++ (Alpha.encode message.rootPartyExecutingTrader
    ++ (Alpha.encode message.rootPartyEnteringTrader
    ++ (Alpha.encode message.targetPartyExecutingFirm
    ++ (Alpha.encode message.targetPartyExecutingTrader
    ++ (Alpha.encode message.firmTradeId
    ++ (Alpha.encode message.firmNegotiationId
    ++ (Alpha.encode message.freeText1
    ++ (Alpha.encode message.freeText2
    ++ (Alpha.encode message.freeText4
    ++ (Alpha.encode message.pad7
    ++ (encodeMany OrderBookItemGrpComp.encode message.orderBookItemGrpComp.val)))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (XetraEnLightCreateDealNotification × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderComp, bytes) ← RbcHeaderComp.decode bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  let (lastQty, bytes) ← decodeUIntLE 8 bytes
  let (quoteId, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (partyIdClientId, bytes) ← decodeUIntLE 8 bytes
  let (partyIdInvestmentDecisionMaker, bytes) ← decodeUIntLE 8 bytes
  let (executingTrader, bytes) ← decodeUIntLE 8 bytes
  let (negotiationId, bytes) ← decodeUIntLE 4 bytes
  let (tradeId, bytes) ← decodeUIntLE 4 bytes
  let (settlDate, bytes) ← decodeUIntLE 4 bytes
  let (tradingCapacity, bytes) ← decodeUInt 1 bytes
  let (trdRptStatus, bytes) ← decodeUInt 1 bytes
  let (messageEventSource, bytes) ← MessageEventSource.decode bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (allocMethod, bytes) ← decodeUInt 1 bytes
  let (noOrderBookItems, bytes) ← decodeUInt 1 bytes
  let (orderAttributeLiquidityProvision, bytes) ← decodeUInt 1 bytes
  let (executingTraderQualifier, bytes) ← decodeUInt 1 bytes
  let (partyIdInvestmentDecisionMakerQualifier, bytes) ← decodeUInt 1 bytes
  let (rootPartyExecutingFirm, bytes) ← Alpha.decode 5 bytes
  let (rootPartyExecutingTrader, bytes) ← Alpha.decode 6 bytes
  let (rootPartyEnteringTrader, bytes) ← Alpha.decode 6 bytes
  let (targetPartyExecutingFirm, bytes) ← Alpha.decode 5 bytes
  let (targetPartyExecutingTrader, bytes) ← Alpha.decode 6 bytes
  let (firmTradeId, bytes) ← Alpha.decode 20 bytes
  let (firmNegotiationId, bytes) ← Alpha.decode 20 bytes
  let (freeText1, bytes) ← Alpha.decode 12 bytes
  let (freeText2, bytes) ← Alpha.decode 12 bytes
  let (freeText4, bytes) ← Alpha.decode 16 bytes
  let (pad7, bytes) ← Alpha.decode 7 bytes
  let (orderBookItemGrpComp_, bytes) ← decodeMany OrderBookItemGrpComp.decode noOrderBookItems.toNat bytes
  if fits_orderBookItemGrpComp : orderBookItemGrpComp_.length < 256 ^ 1 then
    pure ({ pad2, rbcHeaderComp, transactTime, lastPx, lastQty, quoteId, securityId, partyIdClientId, partyIdInvestmentDecisionMaker, executingTrader, negotiationId, tradeId, settlDate, tradingCapacity, trdRptStatus, messageEventSource, side, allocMethod, orderAttributeLiquidityProvision, executingTraderQualifier, partyIdInvestmentDecisionMakerQualifier, rootPartyExecutingFirm, rootPartyExecutingTrader, rootPartyEnteringTrader, targetPartyExecutingFirm, targetPartyExecutingTrader, firmTradeId, firmNegotiationId, freeText1, freeText2, freeText4, pad7, orderBookItemGrpComp := ⟨orderBookItemGrpComp_, fits_orderBookItemGrpComp⟩ }, bytes)
  else none

theorem encode_length_pos (message : XetraEnLightCreateDealNotification) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : XetraEnLightCreateDealNotification) : (encode message).length ≤ 10434 := by
  have bound_orderBookItemGrpComp := message.orderBookItemGrpComp.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, RbcHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length, MessageEventSource.encode_length, encodeMany_length_const OrderBookItemGrpComp.encode 40 OrderBookItemGrpComp.encode_length]
  omega

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : XetraEnLightCreateDealNotification) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RbcHeaderComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
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
  rw [List.append_assoc, MessageEventSource.decode_encode, some_bind]
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
  rw [decodeMany_bounded 1 OrderBookItemGrpComp.encode OrderBookItemGrpComp.decode OrderBookItemGrpComp.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.orderBookItemGrpComp.length_lt]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : XetraEnLightCreateDealNotification) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end XetraEnLightCreateDealNotification

/-- Xetra En Light Deal Response: 98 bytes -/
structure XetraEnLightDealResponse where
  pad2 : Alpha 2
  responseHeaderComp : ResponseHeaderComp
  securityId : BitVec 64
  quoteId : BitVec 64
  negotiationId : BitVec 32
  tradeId : BitVec 32
  secondaryTradeId : BitVec 32
  firmTradeId : Alpha 20
  firmNegotiationId : Alpha 20
  pad4 : Alpha 4
  deriving DecidableEq, Repr

namespace XetraEnLightDealResponse

def encode (message : XetraEnLightDealResponse) : List UInt8 :=
  Alpha.encode message.pad2
    ++ (ResponseHeaderComp.encode message.responseHeaderComp
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.quoteId
    ++ (encodeUIntLE 4 message.negotiationId
    ++ (encodeUIntLE 4 message.tradeId
    ++ (encodeUIntLE 4 message.secondaryTradeId
    ++ (Alpha.encode message.firmTradeId
    ++ (Alpha.encode message.firmNegotiationId
    ++ (Alpha.encode message.pad4)))))))))

def decode (bytes : List UInt8) : Option (XetraEnLightDealResponse × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (responseHeaderComp, bytes) ← ResponseHeaderComp.decode bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (quoteId, bytes) ← decodeUIntLE 8 bytes
  let (negotiationId, bytes) ← decodeUIntLE 4 bytes
  let (tradeId, bytes) ← decodeUIntLE 4 bytes
  let (secondaryTradeId, bytes) ← decodeUIntLE 4 bytes
  let (firmTradeId, bytes) ← Alpha.decode 20 bytes
  let (firmNegotiationId, bytes) ← Alpha.decode 20 bytes
  let (pad4, bytes) ← Alpha.decode 4 bytes
  pure ({ pad2, responseHeaderComp, securityId, quoteId, negotiationId, tradeId, secondaryTradeId, firmTradeId, firmNegotiationId, pad4 }, bytes)

@[simp] theorem encode_length (message : XetraEnLightDealResponse) : (encode message).length = 98 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, ResponseHeaderComp.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : XetraEnLightDealResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : XetraEnLightDealResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ResponseHeaderComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
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

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : XetraEnLightDealResponse) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end XetraEnLightDealResponse

/-- Xetra En Light Negotiation Notification: 266 bytes -/
structure XetraEnLightNegotiationNotification where
  pad2 : Alpha 2
  rbcHeaderComp : RbcHeaderComp
  transactTime : BitVec 64
  bidPx : BitVec 64
  offerPx : BitVec 64
  leavesQty : BitVec 64
  negotiationId : BitVec 32
  numberOfRespondents : BitVec 32
  settlDate : BitVec 32
  quoteStatus : BitVec 8
  side : BitVec 8
  partyExecutingFirm : Alpha 5
  partyExecutingTrader : Alpha 6
  partyEnteringTrader : Alpha 6
  targetPartyExecutingFirm : Alpha 5
  targetPartyExecutingTrader : Alpha 6
  firmNegotiationId : Alpha 20
  freeText5 : Alpha 132
  pad6 : Alpha 6
  deriving DecidableEq, Repr

namespace XetraEnLightNegotiationNotification

def encode (message : XetraEnLightNegotiationNotification) : List UInt8 :=
  Alpha.encode message.pad2
    ++ (RbcHeaderComp.encode message.rbcHeaderComp
    ++ (encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 8 message.bidPx
    ++ (encodeUIntLE 8 message.offerPx
    ++ (encodeUIntLE 8 message.leavesQty
    ++ (encodeUIntLE 4 message.negotiationId
    ++ (encodeUIntLE 4 message.numberOfRespondents
    ++ (encodeUIntLE 4 message.settlDate
    ++ (encodeUInt 1 message.quoteStatus
    ++ (encodeUInt 1 message.side
    ++ (Alpha.encode message.partyExecutingFirm
    ++ (Alpha.encode message.partyExecutingTrader
    ++ (Alpha.encode message.partyEnteringTrader
    ++ (Alpha.encode message.targetPartyExecutingFirm
    ++ (Alpha.encode message.targetPartyExecutingTrader
    ++ (Alpha.encode message.firmNegotiationId
    ++ (Alpha.encode message.freeText5
    ++ (Alpha.encode message.pad6))))))))))))))))))

def decode (bytes : List UInt8) : Option (XetraEnLightNegotiationNotification × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderComp, bytes) ← RbcHeaderComp.decode bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (bidPx, bytes) ← decodeUIntLE 8 bytes
  let (offerPx, bytes) ← decodeUIntLE 8 bytes
  let (leavesQty, bytes) ← decodeUIntLE 8 bytes
  let (negotiationId, bytes) ← decodeUIntLE 4 bytes
  let (numberOfRespondents, bytes) ← decodeUIntLE 4 bytes
  let (settlDate, bytes) ← decodeUIntLE 4 bytes
  let (quoteStatus, bytes) ← decodeUInt 1 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (partyExecutingFirm, bytes) ← Alpha.decode 5 bytes
  let (partyExecutingTrader, bytes) ← Alpha.decode 6 bytes
  let (partyEnteringTrader, bytes) ← Alpha.decode 6 bytes
  let (targetPartyExecutingFirm, bytes) ← Alpha.decode 5 bytes
  let (targetPartyExecutingTrader, bytes) ← Alpha.decode 6 bytes
  let (firmNegotiationId, bytes) ← Alpha.decode 20 bytes
  let (freeText5, bytes) ← Alpha.decode 132 bytes
  let (pad6, bytes) ← Alpha.decode 6 bytes
  pure ({ pad2, rbcHeaderComp, transactTime, bidPx, offerPx, leavesQty, negotiationId, numberOfRespondents, settlDate, quoteStatus, side, partyExecutingFirm, partyExecutingTrader, partyEnteringTrader, targetPartyExecutingFirm, targetPartyExecutingTrader, firmNegotiationId, freeText5, pad6 }, bytes)

@[simp] theorem encode_length (message : XetraEnLightNegotiationNotification) : (encode message).length = 266 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RbcHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : XetraEnLightNegotiationNotification) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : XetraEnLightNegotiationNotification) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RbcHeaderComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
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

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : XetraEnLightNegotiationNotification) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end XetraEnLightNegotiationNotification

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

/-- Xetra En Light Negotiation Requester Notification -/
structure XetraEnLightNegotiationRequesterNotification where
  pad2 : Alpha 2
  rbcHeaderComp : RbcHeaderComp
  transactTime : BitVec 64
  trdRegTsExecutionTime : BitVec 64
  bidPx : BitVec 64
  offerPx : BitVec 64
  orderQty : BitVec 64
  lastPx : BitVec 64
  leavesQty : BitVec 64
  lastQty : BitVec 64
  negotiationId : BitVec 32
  numberOfRespondents : BitVec 32
  settlDate : BitVec 32
  quoteStatus : BitVec 8
  numberOfRespDisclosureInstruction : BitVec 8
  side : BitVec 8
  partyExecutingFirm : Alpha 5
  partyExecutingTrader : Alpha 6
  partyEnteringTrader : Alpha 6
  firmNegotiationId : Alpha 20
  freeText5 : Alpha 132
  pad7 : Alpha 7
  xetraEnLightTargetPartiesComp : Bounded 1 XetraEnLightTargetPartiesComp
  deriving DecidableEq, Repr

namespace XetraEnLightNegotiationRequesterNotification

def encode (message : XetraEnLightNegotiationRequesterNotification) : List UInt8 :=
  Alpha.encode message.pad2
    ++ (RbcHeaderComp.encode message.rbcHeaderComp
    ++ (encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 8 message.trdRegTsExecutionTime
    ++ (encodeUIntLE 8 message.bidPx
    ++ (encodeUIntLE 8 message.offerPx
    ++ (encodeUIntLE 8 message.orderQty
    ++ (encodeUIntLE 8 message.lastPx
    ++ (encodeUIntLE 8 message.leavesQty
    ++ (encodeUIntLE 8 message.lastQty
    ++ (encodeUIntLE 4 message.negotiationId
    ++ (encodeUIntLE 4 message.numberOfRespondents
    ++ (encodeUIntLE 4 message.settlDate
    ++ (encodeUInt 1 message.quoteStatus
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.xetraEnLightTargetPartiesComp.val.length)
    ++ (encodeUInt 1 message.numberOfRespDisclosureInstruction
    ++ (encodeUInt 1 message.side
    ++ (Alpha.encode message.partyExecutingFirm
    ++ (Alpha.encode message.partyExecutingTrader
    ++ (Alpha.encode message.partyEnteringTrader
    ++ (Alpha.encode message.firmNegotiationId
    ++ (Alpha.encode message.freeText5
    ++ (Alpha.encode message.pad7
    ++ (encodeMany XetraEnLightTargetPartiesComp.encode message.xetraEnLightTargetPartiesComp.val)))))))))))))))))))))))

def decode (bytes : List UInt8) : Option (XetraEnLightNegotiationRequesterNotification × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderComp, bytes) ← RbcHeaderComp.decode bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (trdRegTsExecutionTime, bytes) ← decodeUIntLE 8 bytes
  let (bidPx, bytes) ← decodeUIntLE 8 bytes
  let (offerPx, bytes) ← decodeUIntLE 8 bytes
  let (orderQty, bytes) ← decodeUIntLE 8 bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  let (leavesQty, bytes) ← decodeUIntLE 8 bytes
  let (lastQty, bytes) ← decodeUIntLE 8 bytes
  let (negotiationId, bytes) ← decodeUIntLE 4 bytes
  let (numberOfRespondents, bytes) ← decodeUIntLE 4 bytes
  let (settlDate, bytes) ← decodeUIntLE 4 bytes
  let (quoteStatus, bytes) ← decodeUInt 1 bytes
  let (noTargetPartyIDs, bytes) ← decodeUInt 1 bytes
  let (numberOfRespDisclosureInstruction, bytes) ← decodeUInt 1 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (partyExecutingFirm, bytes) ← Alpha.decode 5 bytes
  let (partyExecutingTrader, bytes) ← Alpha.decode 6 bytes
  let (partyEnteringTrader, bytes) ← Alpha.decode 6 bytes
  let (firmNegotiationId, bytes) ← Alpha.decode 20 bytes
  let (freeText5, bytes) ← Alpha.decode 132 bytes
  let (pad7, bytes) ← Alpha.decode 7 bytes
  let (xetraEnLightTargetPartiesComp_, bytes) ← decodeMany XetraEnLightTargetPartiesComp.decode noTargetPartyIDs.toNat bytes
  if fits_xetraEnLightTargetPartiesComp : xetraEnLightTargetPartiesComp_.length < 256 ^ 1 then
    pure ({ pad2, rbcHeaderComp, transactTime, trdRegTsExecutionTime, bidPx, offerPx, orderQty, lastPx, leavesQty, lastQty, negotiationId, numberOfRespondents, settlDate, quoteStatus, numberOfRespDisclosureInstruction, side, partyExecutingFirm, partyExecutingTrader, partyEnteringTrader, firmNegotiationId, freeText5, pad7, xetraEnLightTargetPartiesComp := ⟨xetraEnLightTargetPartiesComp_, fits_xetraEnLightTargetPartiesComp⟩ }, bytes)
  else none

theorem encode_length_pos (message : XetraEnLightNegotiationRequesterNotification) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : XetraEnLightNegotiationRequesterNotification) : (encode message).length ≤ 4370 := by
  have bound_xetraEnLightTargetPartiesComp := message.xetraEnLightTargetPartiesComp.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, RbcHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const XetraEnLightTargetPartiesComp.encode 16 XetraEnLightTargetPartiesComp.encode_length]
  omega

@[simp] theorem decode_encode (message : XetraEnLightNegotiationRequesterNotification) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RbcHeaderComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
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
  rw [decodeMany_bounded 1 XetraEnLightTargetPartiesComp.encode XetraEnLightTargetPartiesComp.decode XetraEnLightTargetPartiesComp.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.xetraEnLightTargetPartiesComp.length_lt]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : XetraEnLightNegotiationRequesterNotification) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end XetraEnLightNegotiationRequesterNotification

/-- Xetra En Light Negotiation Status Notification: 74 bytes -/
structure XetraEnLightNegotiationStatusNotification where
  pad2 : Alpha 2
  rbcHeaderComp : RbcHeaderComp
  transactTime : BitVec 64
  negotiationId : BitVec 32
  quoteStatus : BitVec 8
  firmNegotiationId : Alpha 20
  pad7 : Alpha 7
  deriving DecidableEq, Repr

namespace XetraEnLightNegotiationStatusNotification

def encode (message : XetraEnLightNegotiationStatusNotification) : List UInt8 :=
  Alpha.encode message.pad2
    ++ (RbcHeaderComp.encode message.rbcHeaderComp
    ++ (encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 4 message.negotiationId
    ++ (encodeUInt 1 message.quoteStatus
    ++ (Alpha.encode message.firmNegotiationId
    ++ (Alpha.encode message.pad7))))))

def decode (bytes : List UInt8) : Option (XetraEnLightNegotiationStatusNotification × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderComp, bytes) ← RbcHeaderComp.decode bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (negotiationId, bytes) ← decodeUIntLE 4 bytes
  let (quoteStatus, bytes) ← decodeUInt 1 bytes
  let (firmNegotiationId, bytes) ← Alpha.decode 20 bytes
  let (pad7, bytes) ← Alpha.decode 7 bytes
  pure ({ pad2, rbcHeaderComp, transactTime, negotiationId, quoteStatus, firmNegotiationId, pad7 }, bytes)

@[simp] theorem encode_length (message : XetraEnLightNegotiationStatusNotification) : (encode message).length = 74 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RbcHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : XetraEnLightNegotiationStatusNotification) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : XetraEnLightNegotiationStatusNotification) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RbcHeaderComp.decode_encode, some_bind]
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

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : XetraEnLightNegotiationStatusNotification) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end XetraEnLightNegotiationStatusNotification

/-- Xetra En Light Open Negotiation Notification: 290 bytes -/
structure XetraEnLightOpenNegotiationNotification where
  pad2 : Alpha 2
  rbcHeaderComp : RbcHeaderComp
  transactTime : BitVec 64
  negotiationStartTime : BitVec 64
  securityId : BitVec 64
  bidPx : BitVec 64
  offerPx : BitVec 64
  leavesQty : BitVec 64
  expireTime : BitVec 64
  negotiationId : BitVec 32
  marketSegmentId : BitVec 32
  numberOfRespondents : BitVec 32
  settlDate : BitVec 32
  quoteStatus : BitVec 8
  side : BitVec 8
  respondentType : BitVec 8
  partyExecutingFirm : Alpha 5
  partyExecutingTrader : Alpha 6
  partyEnteringTrader : Alpha 6
  targetPartyExecutingFirm : Alpha 5
  targetPartyExecutingTrader : Alpha 6
  firmNegotiationId : Alpha 20
  freeText5 : Alpha 132
  pad1 : Alpha 1
  deriving DecidableEq, Repr

namespace XetraEnLightOpenNegotiationNotification

def encode (message : XetraEnLightOpenNegotiationNotification) : List UInt8 :=
  Alpha.encode message.pad2
    ++ (RbcHeaderComp.encode message.rbcHeaderComp
    ++ (encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 8 message.negotiationStartTime
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.bidPx
    ++ (encodeUIntLE 8 message.offerPx
    ++ (encodeUIntLE 8 message.leavesQty
    ++ (encodeUIntLE 8 message.expireTime
    ++ (encodeUIntLE 4 message.negotiationId
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.numberOfRespondents
    ++ (encodeUIntLE 4 message.settlDate
    ++ (encodeUInt 1 message.quoteStatus
    ++ (encodeUInt 1 message.side
    ++ (encodeUInt 1 message.respondentType
    ++ (Alpha.encode message.partyExecutingFirm
    ++ (Alpha.encode message.partyExecutingTrader
    ++ (Alpha.encode message.partyEnteringTrader
    ++ (Alpha.encode message.targetPartyExecutingFirm
    ++ (Alpha.encode message.targetPartyExecutingTrader
    ++ (Alpha.encode message.firmNegotiationId
    ++ (Alpha.encode message.freeText5
    ++ (Alpha.encode message.pad1)))))))))))))))))))))))

def decode (bytes : List UInt8) : Option (XetraEnLightOpenNegotiationNotification × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderComp, bytes) ← RbcHeaderComp.decode bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (negotiationStartTime, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (bidPx, bytes) ← decodeUIntLE 8 bytes
  let (offerPx, bytes) ← decodeUIntLE 8 bytes
  let (leavesQty, bytes) ← decodeUIntLE 8 bytes
  let (expireTime, bytes) ← decodeUIntLE 8 bytes
  let (negotiationId, bytes) ← decodeUIntLE 4 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (numberOfRespondents, bytes) ← decodeUIntLE 4 bytes
  let (settlDate, bytes) ← decodeUIntLE 4 bytes
  let (quoteStatus, bytes) ← decodeUInt 1 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (respondentType, bytes) ← decodeUInt 1 bytes
  let (partyExecutingFirm, bytes) ← Alpha.decode 5 bytes
  let (partyExecutingTrader, bytes) ← Alpha.decode 6 bytes
  let (partyEnteringTrader, bytes) ← Alpha.decode 6 bytes
  let (targetPartyExecutingFirm, bytes) ← Alpha.decode 5 bytes
  let (targetPartyExecutingTrader, bytes) ← Alpha.decode 6 bytes
  let (firmNegotiationId, bytes) ← Alpha.decode 20 bytes
  let (freeText5, bytes) ← Alpha.decode 132 bytes
  let (pad1, bytes) ← Alpha.decode 1 bytes
  pure ({ pad2, rbcHeaderComp, transactTime, negotiationStartTime, securityId, bidPx, offerPx, leavesQty, expireTime, negotiationId, marketSegmentId, numberOfRespondents, settlDate, quoteStatus, side, respondentType, partyExecutingFirm, partyExecutingTrader, partyEnteringTrader, targetPartyExecutingFirm, targetPartyExecutingTrader, firmNegotiationId, freeText5, pad1 }, bytes)

@[simp] theorem encode_length (message : XetraEnLightOpenNegotiationNotification) : (encode message).length = 290 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RbcHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : XetraEnLightOpenNegotiationNotification) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : XetraEnLightOpenNegotiationNotification) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RbcHeaderComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
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

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : XetraEnLightOpenNegotiationNotification) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end XetraEnLightOpenNegotiationNotification

/-- Xetra En Light Open Negotiation Requester Notification -/
structure XetraEnLightOpenNegotiationRequesterNotification where
  pad2 : Alpha 2
  rbcHeaderComp : RbcHeaderComp
  transactTime : BitVec 64
  securityId : BitVec 64
  bidPx : BitVec 64
  offerPx : BitVec 64
  orderQty : BitVec 64
  lastPx : BitVec 64
  lastQty : BitVec 64
  expireTime : BitVec 64
  negotiationId : BitVec 32
  marketSegmentId : BitVec 32
  numberOfRespondents : BitVec 32
  settlDate : BitVec 32
  quoteStatus : BitVec 8
  side : BitVec 8
  numberOfRespDisclosureInstruction : BitVec 8
  respondentType : BitVec 8
  partyExecutingFirm : Alpha 5
  partyExecutingTrader : Alpha 6
  partyEnteringTrader : Alpha 6
  firmNegotiationId : Alpha 20
  freeText5 : Alpha 132
  pad2v2 : Alpha 2
  xetraEnLightTargetPartiesComp : Bounded 1 XetraEnLightTargetPartiesComp
  deriving DecidableEq, Repr

namespace XetraEnLightOpenNegotiationRequesterNotification

def encode (message : XetraEnLightOpenNegotiationRequesterNotification) : List UInt8 :=
  Alpha.encode message.pad2
    ++ (RbcHeaderComp.encode message.rbcHeaderComp
    ++ (encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.bidPx
    ++ (encodeUIntLE 8 message.offerPx
    ++ (encodeUIntLE 8 message.orderQty
    ++ (encodeUIntLE 8 message.lastPx
    ++ (encodeUIntLE 8 message.lastQty
    ++ (encodeUIntLE 8 message.expireTime
    ++ (encodeUIntLE 4 message.negotiationId
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.numberOfRespondents
    ++ (encodeUIntLE 4 message.settlDate
    ++ (encodeUInt 1 message.quoteStatus
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.xetraEnLightTargetPartiesComp.val.length)
    ++ (encodeUInt 1 message.side
    ++ (encodeUInt 1 message.numberOfRespDisclosureInstruction
    ++ (encodeUInt 1 message.respondentType
    ++ (Alpha.encode message.partyExecutingFirm
    ++ (Alpha.encode message.partyExecutingTrader
    ++ (Alpha.encode message.partyEnteringTrader
    ++ (Alpha.encode message.firmNegotiationId
    ++ (Alpha.encode message.freeText5
    ++ (Alpha.encode message.pad2v2
    ++ (encodeMany XetraEnLightTargetPartiesComp.encode message.xetraEnLightTargetPartiesComp.val)))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (XetraEnLightOpenNegotiationRequesterNotification × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderComp, bytes) ← RbcHeaderComp.decode bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (bidPx, bytes) ← decodeUIntLE 8 bytes
  let (offerPx, bytes) ← decodeUIntLE 8 bytes
  let (orderQty, bytes) ← decodeUIntLE 8 bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  let (lastQty, bytes) ← decodeUIntLE 8 bytes
  let (expireTime, bytes) ← decodeUIntLE 8 bytes
  let (negotiationId, bytes) ← decodeUIntLE 4 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (numberOfRespondents, bytes) ← decodeUIntLE 4 bytes
  let (settlDate, bytes) ← decodeUIntLE 4 bytes
  let (quoteStatus, bytes) ← decodeUInt 1 bytes
  let (noTargetPartyIDs, bytes) ← decodeUInt 1 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (numberOfRespDisclosureInstruction, bytes) ← decodeUInt 1 bytes
  let (respondentType, bytes) ← decodeUInt 1 bytes
  let (partyExecutingFirm, bytes) ← Alpha.decode 5 bytes
  let (partyExecutingTrader, bytes) ← Alpha.decode 6 bytes
  let (partyEnteringTrader, bytes) ← Alpha.decode 6 bytes
  let (firmNegotiationId, bytes) ← Alpha.decode 20 bytes
  let (freeText5, bytes) ← Alpha.decode 132 bytes
  let (pad2v2, bytes) ← Alpha.decode 2 bytes
  let (xetraEnLightTargetPartiesComp_, bytes) ← decodeMany XetraEnLightTargetPartiesComp.decode noTargetPartyIDs.toNat bytes
  if fits_xetraEnLightTargetPartiesComp : xetraEnLightTargetPartiesComp_.length < 256 ^ 1 then
    pure ({ pad2, rbcHeaderComp, transactTime, securityId, bidPx, offerPx, orderQty, lastPx, lastQty, expireTime, negotiationId, marketSegmentId, numberOfRespondents, settlDate, quoteStatus, side, numberOfRespDisclosureInstruction, respondentType, partyExecutingFirm, partyExecutingTrader, partyEnteringTrader, firmNegotiationId, freeText5, pad2v2, xetraEnLightTargetPartiesComp := ⟨xetraEnLightTargetPartiesComp_, fits_xetraEnLightTargetPartiesComp⟩ }, bytes)
  else none

theorem encode_length_pos (message : XetraEnLightOpenNegotiationRequesterNotification) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : XetraEnLightOpenNegotiationRequesterNotification) : (encode message).length ≤ 4370 := by
  have bound_xetraEnLightTargetPartiesComp := message.xetraEnLightTargetPartiesComp.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, RbcHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const XetraEnLightTargetPartiesComp.encode 16 XetraEnLightTargetPartiesComp.encode_length]
  omega

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : XetraEnLightOpenNegotiationRequesterNotification) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RbcHeaderComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 XetraEnLightTargetPartiesComp.encode XetraEnLightTargetPartiesComp.decode XetraEnLightTargetPartiesComp.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.xetraEnLightTargetPartiesComp.length_lt]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : XetraEnLightOpenNegotiationRequesterNotification) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end XetraEnLightOpenNegotiationRequesterNotification

/-- Xetra En Light Quote Notification: 178 bytes -/
structure XetraEnLightQuoteNotification where
  pad2 : Alpha 2
  rbcHeaderComp : RbcHeaderComp
  transactTime : BitVec 64
  quoteId : BitVec 64
  secondaryQuoteId : BitVec 64
  bidPx : BitVec 64
  bidSize : BitVec 64
  offerPx : BitVec 64
  offerSize : BitVec 64
  negotiationId : BitVec 32
  tradingCapacity : BitVec 8
  quotingStatus : BitVec 8
  quoteEventReason : BitVec 8
  partyExecutingFirm : Alpha 5
  partyExecutingTrader : Alpha 6
  partyEnteringTrader : Alpha 6
  quoteReqId : Alpha 20
  freeText1 : Alpha 12
  freeText2 : Alpha 12
  freeText4 : Alpha 16
  pad4 : Alpha 4
  deriving DecidableEq, Repr

namespace XetraEnLightQuoteNotification

def encode (message : XetraEnLightQuoteNotification) : List UInt8 :=
  Alpha.encode message.pad2
    ++ (RbcHeaderComp.encode message.rbcHeaderComp
    ++ (encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 8 message.quoteId
    ++ (encodeUIntLE 8 message.secondaryQuoteId
    ++ (encodeUIntLE 8 message.bidPx
    ++ (encodeUIntLE 8 message.bidSize
    ++ (encodeUIntLE 8 message.offerPx
    ++ (encodeUIntLE 8 message.offerSize
    ++ (encodeUIntLE 4 message.negotiationId
    ++ (encodeUInt 1 message.tradingCapacity
    ++ (encodeUInt 1 message.quotingStatus
    ++ (encodeUInt 1 message.quoteEventReason
    ++ (Alpha.encode message.partyExecutingFirm
    ++ (Alpha.encode message.partyExecutingTrader
    ++ (Alpha.encode message.partyEnteringTrader
    ++ (Alpha.encode message.quoteReqId
    ++ (Alpha.encode message.freeText1
    ++ (Alpha.encode message.freeText2
    ++ (Alpha.encode message.freeText4
    ++ (Alpha.encode message.pad4))))))))))))))))))))

def decode (bytes : List UInt8) : Option (XetraEnLightQuoteNotification × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderComp, bytes) ← RbcHeaderComp.decode bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (quoteId, bytes) ← decodeUIntLE 8 bytes
  let (secondaryQuoteId, bytes) ← decodeUIntLE 8 bytes
  let (bidPx, bytes) ← decodeUIntLE 8 bytes
  let (bidSize, bytes) ← decodeUIntLE 8 bytes
  let (offerPx, bytes) ← decodeUIntLE 8 bytes
  let (offerSize, bytes) ← decodeUIntLE 8 bytes
  let (negotiationId, bytes) ← decodeUIntLE 4 bytes
  let (tradingCapacity, bytes) ← decodeUInt 1 bytes
  let (quotingStatus, bytes) ← decodeUInt 1 bytes
  let (quoteEventReason, bytes) ← decodeUInt 1 bytes
  let (partyExecutingFirm, bytes) ← Alpha.decode 5 bytes
  let (partyExecutingTrader, bytes) ← Alpha.decode 6 bytes
  let (partyEnteringTrader, bytes) ← Alpha.decode 6 bytes
  let (quoteReqId, bytes) ← Alpha.decode 20 bytes
  let (freeText1, bytes) ← Alpha.decode 12 bytes
  let (freeText2, bytes) ← Alpha.decode 12 bytes
  let (freeText4, bytes) ← Alpha.decode 16 bytes
  let (pad4, bytes) ← Alpha.decode 4 bytes
  pure ({ pad2, rbcHeaderComp, transactTime, quoteId, secondaryQuoteId, bidPx, bidSize, offerPx, offerSize, negotiationId, tradingCapacity, quotingStatus, quoteEventReason, partyExecutingFirm, partyExecutingTrader, partyEnteringTrader, quoteReqId, freeText1, freeText2, freeText4, pad4 }, bytes)

@[simp] theorem encode_length (message : XetraEnLightQuoteNotification) : (encode message).length = 178 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RbcHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : XetraEnLightQuoteNotification) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : XetraEnLightQuoteNotification) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RbcHeaderComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
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

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : XetraEnLightQuoteNotification) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end XetraEnLightQuoteNotification

/-- Srqs Quote Entry Grp Comp: 80 bytes -/
structure SrqsQuoteEntryGrpComp where
  transactTime : BitVec 64
  quoteId : BitVec 64
  secondaryQuoteId : BitVec 64
  bidPx : BitVec 64
  bidSize : BitVec 64
  offerPx : BitVec 64
  offerSize : BitVec 64
  partyIdExecutingTrader : BitVec 32
  quotingStatus : BitVec 8
  partyExecutingFirm : Alpha 5
  partyExecutingTrader : Alpha 6
  partyEnteringTrader : Alpha 6
  pad2 : Alpha 2
  deriving DecidableEq, Repr

namespace SrqsQuoteEntryGrpComp

def encode (message : SrqsQuoteEntryGrpComp) : List UInt8 :=
  encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 8 message.quoteId
    ++ (encodeUIntLE 8 message.secondaryQuoteId
    ++ (encodeUIntLE 8 message.bidPx
    ++ (encodeUIntLE 8 message.bidSize
    ++ (encodeUIntLE 8 message.offerPx
    ++ (encodeUIntLE 8 message.offerSize
    ++ (encodeUIntLE 4 message.partyIdExecutingTrader
    ++ (encodeUInt 1 message.quotingStatus
    ++ (Alpha.encode message.partyExecutingFirm
    ++ (Alpha.encode message.partyExecutingTrader
    ++ (Alpha.encode message.partyEnteringTrader
    ++ (Alpha.encode message.pad2))))))))))))

def decode (bytes : List UInt8) : Option (SrqsQuoteEntryGrpComp × List UInt8) := do
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (quoteId, bytes) ← decodeUIntLE 8 bytes
  let (secondaryQuoteId, bytes) ← decodeUIntLE 8 bytes
  let (bidPx, bytes) ← decodeUIntLE 8 bytes
  let (bidSize, bytes) ← decodeUIntLE 8 bytes
  let (offerPx, bytes) ← decodeUIntLE 8 bytes
  let (offerSize, bytes) ← decodeUIntLE 8 bytes
  let (partyIdExecutingTrader, bytes) ← decodeUIntLE 4 bytes
  let (quotingStatus, bytes) ← decodeUInt 1 bytes
  let (partyExecutingFirm, bytes) ← Alpha.decode 5 bytes
  let (partyExecutingTrader, bytes) ← Alpha.decode 6 bytes
  let (partyEnteringTrader, bytes) ← Alpha.decode 6 bytes
  let (pad2, bytes) ← Alpha.decode 2 bytes
  pure ({ transactTime, quoteId, secondaryQuoteId, bidPx, bidSize, offerPx, offerSize, partyIdExecutingTrader, quotingStatus, partyExecutingFirm, partyExecutingTrader, partyEnteringTrader, pad2 }, bytes)

@[simp] theorem encode_length (message : SrqsQuoteEntryGrpComp) : (encode message).length = 80 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : SrqsQuoteEntryGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SrqsQuoteEntryGrpComp) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end SrqsQuoteEntryGrpComp

/-- Xetra En Light Quote Requester Notification -/
structure XetraEnLightQuoteRequesterNotification where
  pad2 : Alpha 2
  rbcHeaderComp : RbcHeaderComp
  transactTime : BitVec 64
  negotiationId : BitVec 32
  tradeId : BitVec 32
  quoteReqId : Alpha 20
  pad3 : Alpha 3
  srqsQuoteEntryGrpComp : Bounded 1 SrqsQuoteEntryGrpComp
  deriving DecidableEq, Repr

namespace XetraEnLightQuoteRequesterNotification

def encode (message : XetraEnLightQuoteRequesterNotification) : List UInt8 :=
  Alpha.encode message.pad2
    ++ (RbcHeaderComp.encode message.rbcHeaderComp
    ++ (encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 4 message.negotiationId
    ++ (encodeUIntLE 4 message.tradeId
    ++ (Alpha.encode message.quoteReqId
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.srqsQuoteEntryGrpComp.val.length)
    ++ (Alpha.encode message.pad3
    ++ (encodeMany SrqsQuoteEntryGrpComp.encode message.srqsQuoteEntryGrpComp.val))))))))

def decode (bytes : List UInt8) : Option (XetraEnLightQuoteRequesterNotification × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderComp, bytes) ← RbcHeaderComp.decode bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (negotiationId, bytes) ← decodeUIntLE 4 bytes
  let (tradeId, bytes) ← decodeUIntLE 4 bytes
  let (quoteReqId, bytes) ← Alpha.decode 20 bytes
  let (noQuoteEntries, bytes) ← decodeUInt 1 bytes
  let (pad3, bytes) ← Alpha.decode 3 bytes
  let (srqsQuoteEntryGrpComp_, bytes) ← decodeMany SrqsQuoteEntryGrpComp.decode noQuoteEntries.toNat bytes
  if fits_srqsQuoteEntryGrpComp : srqsQuoteEntryGrpComp_.length < 256 ^ 1 then
    pure ({ pad2, rbcHeaderComp, transactTime, negotiationId, tradeId, quoteReqId, pad3, srqsQuoteEntryGrpComp := ⟨srqsQuoteEntryGrpComp_, fits_srqsQuoteEntryGrpComp⟩ }, bytes)
  else none

theorem encode_length_pos (message : XetraEnLightQuoteRequesterNotification) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : XetraEnLightQuoteRequesterNotification) : (encode message).length ≤ 20474 := by
  have bound_srqsQuoteEntryGrpComp := message.srqsQuoteEntryGrpComp.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, RbcHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const SrqsQuoteEntryGrpComp.encode 80 SrqsQuoteEntryGrpComp.encode_length]
  omega

@[simp] theorem decode_encode (message : XetraEnLightQuoteRequesterNotification) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RbcHeaderComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 SrqsQuoteEntryGrpComp.encode SrqsQuoteEntryGrpComp.decode SrqsQuoteEntryGrpComp.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.srqsQuoteEntryGrpComp.length_lt]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : XetraEnLightQuoteRequesterNotification) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end XetraEnLightQuoteRequesterNotification

/-- Xetra En Light Quote Response: 58 bytes -/
structure XetraEnLightQuoteResponse where
  pad2 : Alpha 2
  responseHeaderComp : ResponseHeaderComp
  quoteId : BitVec 64
  negotiationId : BitVec 32
  quoteReqId : Alpha 20
  deriving DecidableEq, Repr

namespace XetraEnLightQuoteResponse

def encode (message : XetraEnLightQuoteResponse) : List UInt8 :=
  Alpha.encode message.pad2
    ++ (ResponseHeaderComp.encode message.responseHeaderComp
    ++ (encodeUIntLE 8 message.quoteId
    ++ (encodeUIntLE 4 message.negotiationId
    ++ (Alpha.encode message.quoteReqId))))

def decode (bytes : List UInt8) : Option (XetraEnLightQuoteResponse × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (responseHeaderComp, bytes) ← ResponseHeaderComp.decode bytes
  let (quoteId, bytes) ← decodeUIntLE 8 bytes
  let (negotiationId, bytes) ← decodeUIntLE 4 bytes
  let (quoteReqId, bytes) ← Alpha.decode 20 bytes
  pure ({ pad2, responseHeaderComp, quoteId, negotiationId, quoteReqId }, bytes)

@[simp] theorem encode_length (message : XetraEnLightQuoteResponse) : (encode message).length = 58 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, ResponseHeaderComp.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : XetraEnLightQuoteResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : XetraEnLightQuoteResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, ResponseHeaderComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : XetraEnLightQuoteResponse) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end XetraEnLightQuoteResponse

/-- Xetra En Light Status Broadcast: 42 bytes -/
structure XetraEnLightStatusBroadcast where
  pad2 : Alpha 2
  rbcHeaderComp : RbcHeaderComp
  tradeDate : BitVec 32
  tradSesEvent : BitVec 8
  pad3 : Alpha 3
  deriving DecidableEq, Repr

namespace XetraEnLightStatusBroadcast

def encode (message : XetraEnLightStatusBroadcast) : List UInt8 :=
  Alpha.encode message.pad2
    ++ (RbcHeaderComp.encode message.rbcHeaderComp
    ++ (encodeUIntLE 4 message.tradeDate
    ++ (encodeUInt 1 message.tradSesEvent
    ++ (Alpha.encode message.pad3))))

def decode (bytes : List UInt8) : Option (XetraEnLightStatusBroadcast × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderComp, bytes) ← RbcHeaderComp.decode bytes
  let (tradeDate, bytes) ← decodeUIntLE 4 bytes
  let (tradSesEvent, bytes) ← decodeUInt 1 bytes
  let (pad3, bytes) ← Alpha.decode 3 bytes
  pure ({ pad2, rbcHeaderComp, tradeDate, tradSesEvent, pad3 }, bytes)

@[simp] theorem encode_length (message : XetraEnLightStatusBroadcast) : (encode message).length = 42 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RbcHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : XetraEnLightStatusBroadcast) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : XetraEnLightStatusBroadcast) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, RbcHeaderComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : XetraEnLightStatusBroadcast) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end XetraEnLightStatusBroadcast

/-- Any Server Payload, selected by Template Id -/
inductive ServerPayload where
  | bestQuoteExecutionReport (message : BestQuoteExecutionReport) -- 10414
  | bestQuoteResponse (message : BestQuoteResponse) -- 10413
  | broadcastErrorNotification (message : BroadcastErrorNotification) -- 10032
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
  | extendedDeletionReport (message : ExtendedDeletionReport) -- 10128
  | forcedLogoutNotification (message : ForcedLogoutNotification) -- 10012
  | forcedUserLogoutNotification (message : ForcedUserLogoutNotification) -- 10043
  | heartbeatNotification (message : HeartbeatNotification) -- 10023
  | inquireEnrichmentRuleIdListResponse (message : InquireEnrichmentRuleIdListResponse) -- 10041
  | inquireSessionListResponse (message : InquireSessionListResponse) -- 10036
  | inquireUserResponse (message : InquireUserResponse) -- 10039
  | issuerNotification (message : IssuerNotification) -- 10316
  | issuerSecurityStateChangeResponse (message : IssuerSecurityStateChangeResponse) -- 10315
  | legalNotificationBroadcast (message : LegalNotificationBroadcast) -- 10037
  | logonResponse (message : LogonResponse) -- 10001
  | logoutResponse (message : LogoutResponse) -- 10003
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
  | quoteActivationNotification (message : QuoteActivationNotification) -- 10411
  | quoteActivationResponse (message : QuoteActivationResponse) -- 10404
  | quoteExecutionReport (message : QuoteExecutionReport) -- 10407
  | rfqBroadcast (message : RfqBroadcast) -- 10415
  | rfqRejectNotification (message : RfqRejectNotification) -- 10420
  | rfqResponse (message : RfqResponse) -- 10402
  | rfqSpecialistBroadcast (message : RfqSpecialistBroadcast) -- 10419
  | reject (message : Reject) -- 10010
  | retransmitMeMessageResponse (message : RetransmitMeMessageResponse) -- 10027
  | retransmitResponse (message : RetransmitResponse) -- 10009
  | serviceAvailabilityBroadcast (message : ServiceAvailabilityBroadcast) -- 10030
  | serviceAvailabilityMarketBroadcast (message : ServiceAvailabilityMarketBroadcast) -- 10044
  | specialistDeleteAllOrderBroadcast (message : SpecialistDeleteAllOrderBroadcast) -- 10137
  | specialistInstrumentEventNotification (message : SpecialistInstrumentEventNotification) -- 10319
  | specialistOrderBookNotification (message : SpecialistOrderBookNotification) -- 10136
  | specialistRfqReplyNotification (message : SpecialistRfqReplyNotification) -- 10424
  | specialistRfqReplyResponse (message : SpecialistRfqReplyResponse) -- 10423
  | specialistSecurityStateChangeResponse (message : SpecialistSecurityStateChangeResponse) -- 10318
  | subscribeResponse (message : SubscribeResponse) -- 10005
  | tesApproveBroadcast (message : TesApproveBroadcast) -- 10607
  | tesBroadcast (message : TesBroadcast) -- 10604
  | tesDeleteBroadcast (message : TesDeleteBroadcast) -- 10606
  | tesExecutionBroadcast (message : TesExecutionBroadcast) -- 10610
  | tesResponse (message : TesResponse) -- 10611
  | tesTradeBroadcast (message : TesTradeBroadcast) -- 10614
  | tesTradingSessionStatusBroadcast (message : TesTradingSessionStatusBroadcast) -- 10615
  | tmTradingSessionStatusBroadcast (message : TmTradingSessionStatusBroadcast) -- 10501
  | throttleUpdateNotification (message : ThrottleUpdateNotification) -- 10028
  | tradeBroadcast (message : TradeBroadcast) -- 10500
  | tradingSessionStatusBroadcast (message : TradingSessionStatusBroadcast) -- 10307
  | trailingStopUpdateNotification (message : TrailingStopUpdateNotification) -- 10127
  | unsubscribeResponse (message : UnsubscribeResponse) -- 10007
  | userLoginResponse (message : UserLoginResponse) -- 10019
  | userLogoutResponse (message : UserLogoutResponse) -- 10024
  | xetraEnLightCreateDealNotification (message : XetraEnLightCreateDealNotification) -- 10808
  | xetraEnLightDealResponse (message : XetraEnLightDealResponse) -- 10805
  | xetraEnLightNegotiationNotification (message : XetraEnLightNegotiationNotification) -- 10813
  | xetraEnLightNegotiationRequesterNotification (message : XetraEnLightNegotiationRequesterNotification) -- 10812
  | xetraEnLightNegotiationStatusNotification (message : XetraEnLightNegotiationStatusNotification) -- 10815
  | xetraEnLightOpenNegotiationNotification (message : XetraEnLightOpenNegotiationNotification) -- 10811
  | xetraEnLightOpenNegotiationRequesterNotification (message : XetraEnLightOpenNegotiationRequesterNotification) -- 10810
  | xetraEnLightQuoteNotification (message : XetraEnLightQuoteNotification) -- 10807
  | xetraEnLightQuoteRequesterNotification (message : XetraEnLightQuoteRequesterNotification) -- 10816
  | xetraEnLightQuoteResponse (message : XetraEnLightQuoteResponse) -- 10803
  | xetraEnLightStatusBroadcast (message : XetraEnLightStatusBroadcast) -- 10814
  deriving DecidableEq, Repr

namespace ServerPayload

/-- The Template Id each message is sent under -/
def tag : ServerPayload → BitVec 16
  | .bestQuoteExecutionReport _ => 10414
  | .bestQuoteResponse _ => 10413
  | .broadcastErrorNotification _ => 10032
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
  | .extendedDeletionReport _ => 10128
  | .forcedLogoutNotification _ => 10012
  | .forcedUserLogoutNotification _ => 10043
  | .heartbeatNotification _ => 10023
  | .inquireEnrichmentRuleIdListResponse _ => 10041
  | .inquireSessionListResponse _ => 10036
  | .inquireUserResponse _ => 10039
  | .issuerNotification _ => 10316
  | .issuerSecurityStateChangeResponse _ => 10315
  | .legalNotificationBroadcast _ => 10037
  | .logonResponse _ => 10001
  | .logoutResponse _ => 10003
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
  | .quoteActivationNotification _ => 10411
  | .quoteActivationResponse _ => 10404
  | .quoteExecutionReport _ => 10407
  | .rfqBroadcast _ => 10415
  | .rfqRejectNotification _ => 10420
  | .rfqResponse _ => 10402
  | .rfqSpecialistBroadcast _ => 10419
  | .reject _ => 10010
  | .retransmitMeMessageResponse _ => 10027
  | .retransmitResponse _ => 10009
  | .serviceAvailabilityBroadcast _ => 10030
  | .serviceAvailabilityMarketBroadcast _ => 10044
  | .specialistDeleteAllOrderBroadcast _ => 10137
  | .specialistInstrumentEventNotification _ => 10319
  | .specialistOrderBookNotification _ => 10136
  | .specialistRfqReplyNotification _ => 10424
  | .specialistRfqReplyResponse _ => 10423
  | .specialistSecurityStateChangeResponse _ => 10318
  | .subscribeResponse _ => 10005
  | .tesApproveBroadcast _ => 10607
  | .tesBroadcast _ => 10604
  | .tesDeleteBroadcast _ => 10606
  | .tesExecutionBroadcast _ => 10610
  | .tesResponse _ => 10611
  | .tesTradeBroadcast _ => 10614
  | .tesTradingSessionStatusBroadcast _ => 10615
  | .tmTradingSessionStatusBroadcast _ => 10501
  | .throttleUpdateNotification _ => 10028
  | .tradeBroadcast _ => 10500
  | .tradingSessionStatusBroadcast _ => 10307
  | .trailingStopUpdateNotification _ => 10127
  | .unsubscribeResponse _ => 10007
  | .userLoginResponse _ => 10019
  | .userLogoutResponse _ => 10024
  | .xetraEnLightCreateDealNotification _ => 10808
  | .xetraEnLightDealResponse _ => 10805
  | .xetraEnLightNegotiationNotification _ => 10813
  | .xetraEnLightNegotiationRequesterNotification _ => 10812
  | .xetraEnLightNegotiationStatusNotification _ => 10815
  | .xetraEnLightOpenNegotiationNotification _ => 10811
  | .xetraEnLightOpenNegotiationRequesterNotification _ => 10810
  | .xetraEnLightQuoteNotification _ => 10807
  | .xetraEnLightQuoteRequesterNotification _ => 10816
  | .xetraEnLightQuoteResponse _ => 10803
  | .xetraEnLightStatusBroadcast _ => 10814

def encode : ServerPayload → List UInt8
  | .bestQuoteExecutionReport message => BestQuoteExecutionReport.encode message
  | .bestQuoteResponse message => BestQuoteResponse.encode message
  | .broadcastErrorNotification message => BroadcastErrorNotification.encode message
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
  | .extendedDeletionReport message => ExtendedDeletionReport.encode message
  | .forcedLogoutNotification message => ForcedLogoutNotification.encode message
  | .forcedUserLogoutNotification message => ForcedUserLogoutNotification.encode message
  | .heartbeatNotification message => HeartbeatNotification.encode message
  | .inquireEnrichmentRuleIdListResponse message => InquireEnrichmentRuleIdListResponse.encode message
  | .inquireSessionListResponse message => InquireSessionListResponse.encode message
  | .inquireUserResponse message => InquireUserResponse.encode message
  | .issuerNotification message => IssuerNotification.encode message
  | .issuerSecurityStateChangeResponse message => IssuerSecurityStateChangeResponse.encode message
  | .legalNotificationBroadcast message => LegalNotificationBroadcast.encode message
  | .logonResponse message => LogonResponse.encode message
  | .logoutResponse message => LogoutResponse.encode message
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
  | .quoteActivationNotification message => QuoteActivationNotification.encode message
  | .quoteActivationResponse message => QuoteActivationResponse.encode message
  | .quoteExecutionReport message => QuoteExecutionReport.encode message
  | .rfqBroadcast message => RfqBroadcast.encode message
  | .rfqRejectNotification message => RfqRejectNotification.encode message
  | .rfqResponse message => RfqResponse.encode message
  | .rfqSpecialistBroadcast message => RfqSpecialistBroadcast.encode message
  | .reject message => Reject.encode message
  | .retransmitMeMessageResponse message => RetransmitMeMessageResponse.encode message
  | .retransmitResponse message => RetransmitResponse.encode message
  | .serviceAvailabilityBroadcast message => ServiceAvailabilityBroadcast.encode message
  | .serviceAvailabilityMarketBroadcast message => ServiceAvailabilityMarketBroadcast.encode message
  | .specialistDeleteAllOrderBroadcast message => SpecialistDeleteAllOrderBroadcast.encode message
  | .specialistInstrumentEventNotification message => SpecialistInstrumentEventNotification.encode message
  | .specialistOrderBookNotification message => SpecialistOrderBookNotification.encode message
  | .specialistRfqReplyNotification message => SpecialistRfqReplyNotification.encode message
  | .specialistRfqReplyResponse message => SpecialistRfqReplyResponse.encode message
  | .specialistSecurityStateChangeResponse message => SpecialistSecurityStateChangeResponse.encode message
  | .subscribeResponse message => SubscribeResponse.encode message
  | .tesApproveBroadcast message => TesApproveBroadcast.encode message
  | .tesBroadcast message => TesBroadcast.encode message
  | .tesDeleteBroadcast message => TesDeleteBroadcast.encode message
  | .tesExecutionBroadcast message => TesExecutionBroadcast.encode message
  | .tesResponse message => TesResponse.encode message
  | .tesTradeBroadcast message => TesTradeBroadcast.encode message
  | .tesTradingSessionStatusBroadcast message => TesTradingSessionStatusBroadcast.encode message
  | .tmTradingSessionStatusBroadcast message => TmTradingSessionStatusBroadcast.encode message
  | .throttleUpdateNotification message => ThrottleUpdateNotification.encode message
  | .tradeBroadcast message => TradeBroadcast.encode message
  | .tradingSessionStatusBroadcast message => TradingSessionStatusBroadcast.encode message
  | .trailingStopUpdateNotification message => TrailingStopUpdateNotification.encode message
  | .unsubscribeResponse message => UnsubscribeResponse.encode message
  | .userLoginResponse message => UserLoginResponse.encode message
  | .userLogoutResponse message => UserLogoutResponse.encode message
  | .xetraEnLightCreateDealNotification message => XetraEnLightCreateDealNotification.encode message
  | .xetraEnLightDealResponse message => XetraEnLightDealResponse.encode message
  | .xetraEnLightNegotiationNotification message => XetraEnLightNegotiationNotification.encode message
  | .xetraEnLightNegotiationRequesterNotification message => XetraEnLightNegotiationRequesterNotification.encode message
  | .xetraEnLightNegotiationStatusNotification message => XetraEnLightNegotiationStatusNotification.encode message
  | .xetraEnLightOpenNegotiationNotification message => XetraEnLightOpenNegotiationNotification.encode message
  | .xetraEnLightOpenNegotiationRequesterNotification message => XetraEnLightOpenNegotiationRequesterNotification.encode message
  | .xetraEnLightQuoteNotification message => XetraEnLightQuoteNotification.encode message
  | .xetraEnLightQuoteRequesterNotification message => XetraEnLightQuoteRequesterNotification.encode message
  | .xetraEnLightQuoteResponse message => XetraEnLightQuoteResponse.encode message
  | .xetraEnLightStatusBroadcast message => XetraEnLightStatusBroadcast.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : ServerPayload) : (encode message).length ≤ 3145730 := by
  cases message with
  | bestQuoteExecutionReport inner =>
    simp only [encode, BestQuoteExecutionReport.encode_length]
    omega
  | bestQuoteResponse inner =>
    simp only [encode, BestQuoteResponse.encode_length]
    omega
  | broadcastErrorNotification inner =>
    have bound_inner := BroadcastErrorNotification.encode_length_le inner
    simp only [encode]
    omega
  | crossRequestResponse inner =>
    simp only [encode, CrossRequestResponse.encode_length]
    omega
  | deleteAllOrderBroadcast inner =>
    have bound_inner := DeleteAllOrderBroadcast.encode_length_le inner
    simp only [encode]
    omega
  | deleteAllOrderNrResponse inner =>
    simp only [encode, DeleteAllOrderNrResponse.encode_length]
    omega
  | deleteAllOrderQuoteEventBroadcast inner =>
    simp only [encode, DeleteAllOrderQuoteEventBroadcast.encode_length]
    omega
  | deleteAllOrderResponse inner =>
    have bound_inner := DeleteAllOrderResponse.encode_length_le inner
    simp only [encode]
    omega
  | deleteAllQuoteBroadcast inner =>
    have bound_inner := DeleteAllQuoteBroadcast.encode_length_le inner
    simp only [encode]
    omega
  | deleteAllQuoteResponse inner =>
    have bound_inner := DeleteAllQuoteResponse.encode_length_le inner
    simp only [encode]
    omega
  | deleteOrderBroadcast inner =>
    simp only [encode, DeleteOrderBroadcast.encode_length]
    omega
  | deleteOrderNrResponse inner =>
    simp only [encode, DeleteOrderNrResponse.encode_length]
    omega
  | deleteOrderResponse inner =>
    simp only [encode, DeleteOrderResponse.encode_length]
    omega
  | extendedDeletionReport inner =>
    simp only [encode, ExtendedDeletionReport.encode_length]
    omega
  | forcedLogoutNotification inner =>
    have bound_inner := ForcedLogoutNotification.encode_length_le inner
    simp only [encode]
    omega
  | forcedUserLogoutNotification inner =>
    have bound_inner := ForcedUserLogoutNotification.encode_length_le inner
    simp only [encode]
    omega
  | heartbeatNotification inner =>
    simp only [encode, HeartbeatNotification.encode_length]
    omega
  | inquireEnrichmentRuleIdListResponse inner =>
    have bound_inner := InquireEnrichmentRuleIdListResponse.encode_length_le inner
    simp only [encode]
    omega
  | inquireSessionListResponse inner =>
    have bound_inner := InquireSessionListResponse.encode_length_le inner
    simp only [encode]
    omega
  | inquireUserResponse inner =>
    have bound_inner := InquireUserResponse.encode_length_le inner
    simp only [encode]
    omega
  | issuerNotification inner =>
    simp only [encode, IssuerNotification.encode_length]
    omega
  | issuerSecurityStateChangeResponse inner =>
    simp only [encode, IssuerSecurityStateChangeResponse.encode_length]
    omega
  | legalNotificationBroadcast inner =>
    have bound_inner := LegalNotificationBroadcast.encode_length_le inner
    simp only [encode]
    omega
  | logonResponse inner =>
    simp only [encode, LogonResponse.encode_length]
    omega
  | logoutResponse inner =>
    simp only [encode, LogoutResponse.encode_length]
    omega
  | massQuoteResponse inner =>
    have bound_inner := MassQuoteResponse.encode_length_le inner
    simp only [encode]
    omega
  | modifyOrderNrResponse inner =>
    simp only [encode, ModifyOrderNrResponse.encode_length]
    omega
  | modifyOrderResponse inner =>
    simp only [encode, ModifyOrderResponse.encode_length]
    omega
  | newOrderNrResponse inner =>
    simp only [encode, NewOrderNrResponse.encode_length]
    omega
  | newOrderResponse inner =>
    simp only [encode, NewOrderResponse.encode_length]
    omega
  | newsBroadcast inner =>
    have bound_inner := NewsBroadcast.encode_length_le inner
    simp only [encode]
    omega
  | orderExecNotification inner =>
    have bound_inner := OrderExecNotification.encode_length_le inner
    simp only [encode]
    omega
  | orderExecReportBroadcast inner =>
    have bound_inner := OrderExecReportBroadcast.encode_length_le inner
    simp only [encode]
    omega
  | orderExecResponse inner =>
    have bound_inner := OrderExecResponse.encode_length_le inner
    simp only [encode]
    omega
  | partyActionReport inner =>
    simp only [encode, PartyActionReport.encode_length]
    omega
  | partyEntitlementsUpdateReport inner =>
    simp only [encode, PartyEntitlementsUpdateReport.encode_length]
    omega
  | quoteActivationNotification inner =>
    have bound_inner := QuoteActivationNotification.encode_length_le inner
    simp only [encode]
    omega
  | quoteActivationResponse inner =>
    have bound_inner := QuoteActivationResponse.encode_length_le inner
    simp only [encode]
    omega
  | quoteExecutionReport inner =>
    have bound_inner := QuoteExecutionReport.encode_length_le inner
    simp only [encode]
    omega
  | rfqBroadcast inner =>
    simp only [encode, RfqBroadcast.encode_length]
    omega
  | rfqRejectNotification inner =>
    simp only [encode, RfqRejectNotification.encode_length]
    omega
  | rfqResponse inner =>
    simp only [encode, RfqResponse.encode_length]
    omega
  | rfqSpecialistBroadcast inner =>
    simp only [encode, RfqSpecialistBroadcast.encode_length]
    omega
  | reject inner =>
    have bound_inner := Reject.encode_length_le inner
    simp only [encode]
    omega
  | retransmitMeMessageResponse inner =>
    simp only [encode, RetransmitMeMessageResponse.encode_length]
    omega
  | retransmitResponse inner =>
    simp only [encode, RetransmitResponse.encode_length]
    omega
  | serviceAvailabilityBroadcast inner =>
    simp only [encode, ServiceAvailabilityBroadcast.encode_length]
    omega
  | serviceAvailabilityMarketBroadcast inner =>
    simp only [encode, ServiceAvailabilityMarketBroadcast.encode_length]
    omega
  | specialistDeleteAllOrderBroadcast inner =>
    have bound_inner := SpecialistDeleteAllOrderBroadcast.encode_length_le inner
    simp only [encode]
    omega
  | specialistInstrumentEventNotification inner =>
    simp only [encode, SpecialistInstrumentEventNotification.encode_length]
    omega
  | specialistOrderBookNotification inner =>
    have bound_inner := SpecialistOrderBookNotification.encode_length_le inner
    simp only [encode]
    omega
  | specialistRfqReplyNotification inner =>
    simp only [encode, SpecialistRfqReplyNotification.encode_length]
    omega
  | specialistRfqReplyResponse inner =>
    simp only [encode, SpecialistRfqReplyResponse.encode_length]
    omega
  | specialistSecurityStateChangeResponse inner =>
    simp only [encode, SpecialistSecurityStateChangeResponse.encode_length]
    omega
  | subscribeResponse inner =>
    simp only [encode, SubscribeResponse.encode_length]
    omega
  | tesApproveBroadcast inner =>
    simp only [encode, TesApproveBroadcast.encode_length]
    omega
  | tesBroadcast inner =>
    have bound_inner := TesBroadcast.encode_length_le inner
    simp only [encode]
    omega
  | tesDeleteBroadcast inner =>
    simp only [encode, TesDeleteBroadcast.encode_length]
    omega
  | tesExecutionBroadcast inner =>
    simp only [encode, TesExecutionBroadcast.encode_length]
    omega
  | tesResponse inner =>
    simp only [encode, TesResponse.encode_length]
    omega
  | tesTradeBroadcast inner =>
    simp only [encode, TesTradeBroadcast.encode_length]
    omega
  | tesTradingSessionStatusBroadcast inner =>
    simp only [encode, TesTradingSessionStatusBroadcast.encode_length]
    omega
  | tmTradingSessionStatusBroadcast inner =>
    simp only [encode, TmTradingSessionStatusBroadcast.encode_length]
    omega
  | throttleUpdateNotification inner =>
    simp only [encode, ThrottleUpdateNotification.encode_length]
    omega
  | tradeBroadcast inner =>
    simp only [encode, TradeBroadcast.encode_length]
    omega
  | tradingSessionStatusBroadcast inner =>
    simp only [encode, TradingSessionStatusBroadcast.encode_length]
    omega
  | trailingStopUpdateNotification inner =>
    simp only [encode, TrailingStopUpdateNotification.encode_length]
    omega
  | unsubscribeResponse inner =>
    simp only [encode, UnsubscribeResponse.encode_length]
    omega
  | userLoginResponse inner =>
    simp only [encode, UserLoginResponse.encode_length]
    omega
  | userLogoutResponse inner =>
    simp only [encode, UserLogoutResponse.encode_length]
    omega
  | xetraEnLightCreateDealNotification inner =>
    have bound_inner := XetraEnLightCreateDealNotification.encode_length_le inner
    simp only [encode]
    omega
  | xetraEnLightDealResponse inner =>
    simp only [encode, XetraEnLightDealResponse.encode_length]
    omega
  | xetraEnLightNegotiationNotification inner =>
    simp only [encode, XetraEnLightNegotiationNotification.encode_length]
    omega
  | xetraEnLightNegotiationRequesterNotification inner =>
    have bound_inner := XetraEnLightNegotiationRequesterNotification.encode_length_le inner
    simp only [encode]
    omega
  | xetraEnLightNegotiationStatusNotification inner =>
    simp only [encode, XetraEnLightNegotiationStatusNotification.encode_length]
    omega
  | xetraEnLightOpenNegotiationNotification inner =>
    simp only [encode, XetraEnLightOpenNegotiationNotification.encode_length]
    omega
  | xetraEnLightOpenNegotiationRequesterNotification inner =>
    have bound_inner := XetraEnLightOpenNegotiationRequesterNotification.encode_length_le inner
    simp only [encode]
    omega
  | xetraEnLightQuoteNotification inner =>
    simp only [encode, XetraEnLightQuoteNotification.encode_length]
    omega
  | xetraEnLightQuoteRequesterNotification inner =>
    have bound_inner := XetraEnLightQuoteRequesterNotification.encode_length_le inner
    simp only [encode]
    omega
  | xetraEnLightQuoteResponse inner =>
    simp only [encode, XetraEnLightQuoteResponse.encode_length]
    omega
  | xetraEnLightStatusBroadcast inner =>
    simp only [encode, XetraEnLightStatusBroadcast.encode_length]
    omega

/-- Decoded from the whole of the frame: a message that reads to its end takes it all, any other must leave nothing -/
def decode (tag : BitVec 16) (bytes : List UInt8) : Option ServerPayload :=
  if tag = 10414 then (BestQuoteExecutionReport.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.bestQuoteExecutionReport message) else none
  else if tag = 10413 then (BestQuoteResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.bestQuoteResponse message) else none
  else if tag = 10032 then (BroadcastErrorNotification.decode bytes).map fun message => .broadcastErrorNotification message
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
  else if tag = 10128 then (ExtendedDeletionReport.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.extendedDeletionReport message) else none
  else if tag = 10012 then (ForcedLogoutNotification.decode bytes).map fun message => .forcedLogoutNotification message
  else if tag = 10043 then (ForcedUserLogoutNotification.decode bytes).map fun message => .forcedUserLogoutNotification message
  else if tag = 10023 then (HeartbeatNotification.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.heartbeatNotification message) else none
  else if tag = 10041 then (InquireEnrichmentRuleIdListResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.inquireEnrichmentRuleIdListResponse message) else none
  else if tag = 10036 then (InquireSessionListResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.inquireSessionListResponse message) else none
  else if tag = 10039 then (InquireUserResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.inquireUserResponse message) else none
  else if tag = 10316 then (IssuerNotification.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.issuerNotification message) else none
  else if tag = 10315 then (IssuerSecurityStateChangeResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.issuerSecurityStateChangeResponse message) else none
  else if tag = 10037 then (LegalNotificationBroadcast.decode bytes).map fun message => .legalNotificationBroadcast message
  else if tag = 10001 then (LogonResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.logonResponse message) else none
  else if tag = 10003 then (LogoutResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.logoutResponse message) else none
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
  else if tag = 10411 then (QuoteActivationNotification.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.quoteActivationNotification message) else none
  else if tag = 10404 then (QuoteActivationResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.quoteActivationResponse message) else none
  else if tag = 10407 then (QuoteExecutionReport.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.quoteExecutionReport message) else none
  else if tag = 10415 then (RfqBroadcast.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.rfqBroadcast message) else none
  else if tag = 10420 then (RfqRejectNotification.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.rfqRejectNotification message) else none
  else if tag = 10402 then (RfqResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.rfqResponse message) else none
  else if tag = 10419 then (RfqSpecialistBroadcast.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.rfqSpecialistBroadcast message) else none
  else if tag = 10010 then (Reject.decode bytes).map fun message => .reject message
  else if tag = 10027 then (RetransmitMeMessageResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.retransmitMeMessageResponse message) else none
  else if tag = 10009 then (RetransmitResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.retransmitResponse message) else none
  else if tag = 10030 then (ServiceAvailabilityBroadcast.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.serviceAvailabilityBroadcast message) else none
  else if tag = 10044 then (ServiceAvailabilityMarketBroadcast.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.serviceAvailabilityMarketBroadcast message) else none
  else if tag = 10137 then (SpecialistDeleteAllOrderBroadcast.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.specialistDeleteAllOrderBroadcast message) else none
  else if tag = 10319 then (SpecialistInstrumentEventNotification.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.specialistInstrumentEventNotification message) else none
  else if tag = 10136 then (SpecialistOrderBookNotification.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.specialistOrderBookNotification message) else none
  else if tag = 10424 then (SpecialistRfqReplyNotification.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.specialistRfqReplyNotification message) else none
  else if tag = 10423 then (SpecialistRfqReplyResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.specialistRfqReplyResponse message) else none
  else if tag = 10318 then (SpecialistSecurityStateChangeResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.specialistSecurityStateChangeResponse message) else none
  else if tag = 10005 then (SubscribeResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.subscribeResponse message) else none
  else if tag = 10607 then (TesApproveBroadcast.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.tesApproveBroadcast message) else none
  else if tag = 10604 then (TesBroadcast.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.tesBroadcast message) else none
  else if tag = 10606 then (TesDeleteBroadcast.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.tesDeleteBroadcast message) else none
  else if tag = 10610 then (TesExecutionBroadcast.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.tesExecutionBroadcast message) else none
  else if tag = 10611 then (TesResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.tesResponse message) else none
  else if tag = 10614 then (TesTradeBroadcast.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.tesTradeBroadcast message) else none
  else if tag = 10615 then (TesTradingSessionStatusBroadcast.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.tesTradingSessionStatusBroadcast message) else none
  else if tag = 10501 then (TmTradingSessionStatusBroadcast.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.tmTradingSessionStatusBroadcast message) else none
  else if tag = 10028 then (ThrottleUpdateNotification.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.throttleUpdateNotification message) else none
  else if tag = 10500 then (TradeBroadcast.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.tradeBroadcast message) else none
  else if tag = 10307 then (TradingSessionStatusBroadcast.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.tradingSessionStatusBroadcast message) else none
  else if tag = 10127 then (TrailingStopUpdateNotification.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.trailingStopUpdateNotification message) else none
  else if tag = 10007 then (UnsubscribeResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.unsubscribeResponse message) else none
  else if tag = 10019 then (UserLoginResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.userLoginResponse message) else none
  else if tag = 10024 then (UserLogoutResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.userLogoutResponse message) else none
  else if tag = 10808 then (XetraEnLightCreateDealNotification.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.xetraEnLightCreateDealNotification message) else none
  else if tag = 10805 then (XetraEnLightDealResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.xetraEnLightDealResponse message) else none
  else if tag = 10813 then (XetraEnLightNegotiationNotification.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.xetraEnLightNegotiationNotification message) else none
  else if tag = 10812 then (XetraEnLightNegotiationRequesterNotification.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.xetraEnLightNegotiationRequesterNotification message) else none
  else if tag = 10815 then (XetraEnLightNegotiationStatusNotification.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.xetraEnLightNegotiationStatusNotification message) else none
  else if tag = 10811 then (XetraEnLightOpenNegotiationNotification.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.xetraEnLightOpenNegotiationNotification message) else none
  else if tag = 10810 then (XetraEnLightOpenNegotiationRequesterNotification.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.xetraEnLightOpenNegotiationRequesterNotification message) else none
  else if tag = 10807 then (XetraEnLightQuoteNotification.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.xetraEnLightQuoteNotification message) else none
  else if tag = 10816 then (XetraEnLightQuoteRequesterNotification.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.xetraEnLightQuoteRequesterNotification message) else none
  else if tag = 10803 then (XetraEnLightQuoteResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.xetraEnLightQuoteResponse message) else none
  else if tag = 10814 then (XetraEnLightStatusBroadcast.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.xetraEnLightStatusBroadcast message) else none
  else none

theorem decode_encode (message : ServerPayload) :
    decode (tag message) (encode message) = some message := by
  cases message with
  | bestQuoteExecutionReport message => simp [decode, encode, tag, BestQuoteExecutionReport.decode_encode_nil]
  | bestQuoteResponse message => simp [decode, encode, tag, BestQuoteResponse.decode_encode_nil]
  | broadcastErrorNotification message => simp [decode, encode, tag, BroadcastErrorNotification.decode_encode]
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
  | extendedDeletionReport message => simp [decode, encode, tag, ExtendedDeletionReport.decode_encode_nil]
  | forcedLogoutNotification message => simp [decode, encode, tag, ForcedLogoutNotification.decode_encode]
  | forcedUserLogoutNotification message => simp [decode, encode, tag, ForcedUserLogoutNotification.decode_encode]
  | heartbeatNotification message => simp [decode, encode, tag, HeartbeatNotification.decode_encode_nil]
  | inquireEnrichmentRuleIdListResponse message => simp [decode, encode, tag, InquireEnrichmentRuleIdListResponse.decode_encode_nil]
  | inquireSessionListResponse message => simp [decode, encode, tag, InquireSessionListResponse.decode_encode_nil]
  | inquireUserResponse message => simp [decode, encode, tag, InquireUserResponse.decode_encode_nil]
  | issuerNotification message => simp [decode, encode, tag, IssuerNotification.decode_encode_nil]
  | issuerSecurityStateChangeResponse message => simp [decode, encode, tag, IssuerSecurityStateChangeResponse.decode_encode_nil]
  | legalNotificationBroadcast message => simp [decode, encode, tag, LegalNotificationBroadcast.decode_encode]
  | logonResponse message => simp [decode, encode, tag, LogonResponse.decode_encode_nil]
  | logoutResponse message => simp [decode, encode, tag, LogoutResponse.decode_encode_nil]
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
  | quoteActivationNotification message => simp [decode, encode, tag, QuoteActivationNotification.decode_encode_nil]
  | quoteActivationResponse message => simp [decode, encode, tag, QuoteActivationResponse.decode_encode_nil]
  | quoteExecutionReport message => simp [decode, encode, tag, QuoteExecutionReport.decode_encode_nil]
  | rfqBroadcast message => simp [decode, encode, tag, RfqBroadcast.decode_encode_nil]
  | rfqRejectNotification message => simp [decode, encode, tag, RfqRejectNotification.decode_encode_nil]
  | rfqResponse message => simp [decode, encode, tag, RfqResponse.decode_encode_nil]
  | rfqSpecialistBroadcast message => simp [decode, encode, tag, RfqSpecialistBroadcast.decode_encode_nil]
  | reject message => simp [decode, encode, tag, Reject.decode_encode]
  | retransmitMeMessageResponse message => simp [decode, encode, tag, RetransmitMeMessageResponse.decode_encode_nil]
  | retransmitResponse message => simp [decode, encode, tag, RetransmitResponse.decode_encode_nil]
  | serviceAvailabilityBroadcast message => simp [decode, encode, tag, ServiceAvailabilityBroadcast.decode_encode_nil]
  | serviceAvailabilityMarketBroadcast message => simp [decode, encode, tag, ServiceAvailabilityMarketBroadcast.decode_encode_nil]
  | specialistDeleteAllOrderBroadcast message => simp [decode, encode, tag, SpecialistDeleteAllOrderBroadcast.decode_encode_nil]
  | specialistInstrumentEventNotification message => simp [decode, encode, tag, SpecialistInstrumentEventNotification.decode_encode_nil]
  | specialistOrderBookNotification message => simp [decode, encode, tag, SpecialistOrderBookNotification.decode_encode_nil]
  | specialistRfqReplyNotification message => simp [decode, encode, tag, SpecialistRfqReplyNotification.decode_encode_nil]
  | specialistRfqReplyResponse message => simp [decode, encode, tag, SpecialistRfqReplyResponse.decode_encode_nil]
  | specialistSecurityStateChangeResponse message => simp [decode, encode, tag, SpecialistSecurityStateChangeResponse.decode_encode_nil]
  | subscribeResponse message => simp [decode, encode, tag, SubscribeResponse.decode_encode_nil]
  | tesApproveBroadcast message => simp [decode, encode, tag, TesApproveBroadcast.decode_encode_nil]
  | tesBroadcast message => simp [decode, encode, tag, TesBroadcast.decode_encode_nil]
  | tesDeleteBroadcast message => simp [decode, encode, tag, TesDeleteBroadcast.decode_encode_nil]
  | tesExecutionBroadcast message => simp [decode, encode, tag, TesExecutionBroadcast.decode_encode_nil]
  | tesResponse message => simp [decode, encode, tag, TesResponse.decode_encode_nil]
  | tesTradeBroadcast message => simp [decode, encode, tag, TesTradeBroadcast.decode_encode_nil]
  | tesTradingSessionStatusBroadcast message => simp [decode, encode, tag, TesTradingSessionStatusBroadcast.decode_encode_nil]
  | tmTradingSessionStatusBroadcast message => simp [decode, encode, tag, TmTradingSessionStatusBroadcast.decode_encode_nil]
  | throttleUpdateNotification message => simp [decode, encode, tag, ThrottleUpdateNotification.decode_encode_nil]
  | tradeBroadcast message => simp [decode, encode, tag, TradeBroadcast.decode_encode_nil]
  | tradingSessionStatusBroadcast message => simp [decode, encode, tag, TradingSessionStatusBroadcast.decode_encode_nil]
  | trailingStopUpdateNotification message => simp [decode, encode, tag, TrailingStopUpdateNotification.decode_encode_nil]
  | unsubscribeResponse message => simp [decode, encode, tag, UnsubscribeResponse.decode_encode_nil]
  | userLoginResponse message => simp [decode, encode, tag, UserLoginResponse.decode_encode_nil]
  | userLogoutResponse message => simp [decode, encode, tag, UserLogoutResponse.decode_encode_nil]
  | xetraEnLightCreateDealNotification message => simp [decode, encode, tag, XetraEnLightCreateDealNotification.decode_encode_nil]
  | xetraEnLightDealResponse message => simp [decode, encode, tag, XetraEnLightDealResponse.decode_encode_nil]
  | xetraEnLightNegotiationNotification message => simp [decode, encode, tag, XetraEnLightNegotiationNotification.decode_encode_nil]
  | xetraEnLightNegotiationRequesterNotification message => simp [decode, encode, tag, XetraEnLightNegotiationRequesterNotification.decode_encode_nil]
  | xetraEnLightNegotiationStatusNotification message => simp [decode, encode, tag, XetraEnLightNegotiationStatusNotification.decode_encode_nil]
  | xetraEnLightOpenNegotiationNotification message => simp [decode, encode, tag, XetraEnLightOpenNegotiationNotification.decode_encode_nil]
  | xetraEnLightOpenNegotiationRequesterNotification message => simp [decode, encode, tag, XetraEnLightOpenNegotiationRequesterNotification.decode_encode_nil]
  | xetraEnLightQuoteNotification message => simp [decode, encode, tag, XetraEnLightQuoteNotification.decode_encode_nil]
  | xetraEnLightQuoteRequesterNotification message => simp [decode, encode, tag, XetraEnLightQuoteRequesterNotification.decode_encode_nil]
  | xetraEnLightQuoteResponse message => simp [decode, encode, tag, XetraEnLightQuoteResponse.decode_encode_nil]
  | xetraEnLightStatusBroadcast message => simp [decode, encode, tag, XetraEnLightStatusBroadcast.decode_encode_nil]

end ServerPayload

/-- Server Message -/
structure ServerMessage where
  serverPayload : ServerPayload
  deriving DecidableEq, Repr

namespace ServerMessage

def encodeBody (message : ServerMessage) : List UInt8 :=
  encodeUIntLE 2 (ServerPayload.tag message.serverPayload)
    ++ (ServerPayload.encode message.serverPayload)

def decodeBody (bytes : List UInt8) : Option ServerMessage := do
  let (templateId, bytes) ← decodeUIntLE 2 bytes
  let serverPayload ← ServerPayload.decode templateId bytes
  pure { serverPayload }

theorem decodeBody_encodeBody (message : ServerMessage) : decodeBody (encodeBody message) = some message := by
  unfold decodeBody encodeBody
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [ServerPayload.decode_encode, some_bind]
  rfl

/-- Every body fits the length prefix -/
theorem encodeBody_length_lt (message : ServerMessage) : (encodeBody message).length + 4 < 256 ^ 4 := by
  unfold encodeBody
  cases message.serverPayload with
  | bestQuoteExecutionReport inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, BestQuoteExecutionReport.encode_length]
    omega
  | bestQuoteResponse inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, BestQuoteResponse.encode_length]
    omega
  | broadcastErrorNotification inner =>
    have bound_inner := BroadcastErrorNotification.encode_length_le inner
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
  | extendedDeletionReport inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, ExtendedDeletionReport.encode_length]
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
  | inquireSessionListResponse inner =>
    have bound_inner := InquireSessionListResponse.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | inquireUserResponse inner =>
    have bound_inner := InquireUserResponse.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | issuerNotification inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, IssuerNotification.encode_length]
    omega
  | issuerSecurityStateChangeResponse inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, IssuerSecurityStateChangeResponse.encode_length]
    omega
  | legalNotificationBroadcast inner =>
    have bound_inner := LegalNotificationBroadcast.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | logonResponse inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, LogonResponse.encode_length]
    omega
  | logoutResponse inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, LogoutResponse.encode_length]
    omega
  | massQuoteResponse inner =>
    have bound_inner := MassQuoteResponse.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | modifyOrderNrResponse inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, ModifyOrderNrResponse.encode_length]
    omega
  | modifyOrderResponse inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, ModifyOrderResponse.encode_length]
    omega
  | newOrderNrResponse inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, NewOrderNrResponse.encode_length]
    omega
  | newOrderResponse inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, NewOrderResponse.encode_length]
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
  | rfqBroadcast inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, RfqBroadcast.encode_length]
    omega
  | rfqRejectNotification inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, RfqRejectNotification.encode_length]
    omega
  | rfqResponse inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, RfqResponse.encode_length]
    omega
  | rfqSpecialistBroadcast inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, RfqSpecialistBroadcast.encode_length]
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
  | serviceAvailabilityBroadcast inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, ServiceAvailabilityBroadcast.encode_length]
    omega
  | serviceAvailabilityMarketBroadcast inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, ServiceAvailabilityMarketBroadcast.encode_length]
    omega
  | specialistDeleteAllOrderBroadcast inner =>
    have bound_inner := SpecialistDeleteAllOrderBroadcast.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | specialistInstrumentEventNotification inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, SpecialistInstrumentEventNotification.encode_length]
    omega
  | specialistOrderBookNotification inner =>
    have bound_inner := SpecialistOrderBookNotification.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | specialistRfqReplyNotification inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, SpecialistRfqReplyNotification.encode_length]
    omega
  | specialistRfqReplyResponse inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, SpecialistRfqReplyResponse.encode_length]
    omega
  | specialistSecurityStateChangeResponse inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, SpecialistSecurityStateChangeResponse.encode_length]
    omega
  | subscribeResponse inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, SubscribeResponse.encode_length]
    omega
  | tesApproveBroadcast inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, TesApproveBroadcast.encode_length]
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
  | tesTradeBroadcast inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, TesTradeBroadcast.encode_length]
    omega
  | tesTradingSessionStatusBroadcast inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, TesTradingSessionStatusBroadcast.encode_length]
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
  | trailingStopUpdateNotification inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, TrailingStopUpdateNotification.encode_length]
    omega
  | unsubscribeResponse inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, UnsubscribeResponse.encode_length]
    omega
  | userLoginResponse inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, UserLoginResponse.encode_length]
    omega
  | userLogoutResponse inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, UserLogoutResponse.encode_length]
    omega
  | xetraEnLightCreateDealNotification inner =>
    have bound_inner := XetraEnLightCreateDealNotification.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | xetraEnLightDealResponse inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, XetraEnLightDealResponse.encode_length]
    omega
  | xetraEnLightNegotiationNotification inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, XetraEnLightNegotiationNotification.encode_length]
    omega
  | xetraEnLightNegotiationRequesterNotification inner =>
    have bound_inner := XetraEnLightNegotiationRequesterNotification.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | xetraEnLightNegotiationStatusNotification inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, XetraEnLightNegotiationStatusNotification.encode_length]
    omega
  | xetraEnLightOpenNegotiationNotification inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, XetraEnLightOpenNegotiationNotification.encode_length]
    omega
  | xetraEnLightOpenNegotiationRequesterNotification inner =>
    have bound_inner := XetraEnLightOpenNegotiationRequesterNotification.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | xetraEnLightQuoteNotification inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, XetraEnLightQuoteNotification.encode_length]
    omega
  | xetraEnLightQuoteRequesterNotification inner =>
    have bound_inner := XetraEnLightQuoteRequesterNotification.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | xetraEnLightQuoteResponse inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, XetraEnLightQuoteResponse.encode_length]
    omega
  | xetraEnLightStatusBroadcast inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, XetraEnLightStatusBroadcast.encode_length]
    omega

/-- Size rule: Body Len counts the bytes after it plus 4, so it is written from the body and checked on decode -/
def encode : ServerMessage → List UInt8 :=
  encodeFramedLE 4 4 encodeBody

def decode : List UInt8 → Option (ServerMessage × List UInt8) :=
  decodeFramedAllLE 4 4 decodeBody

@[simp] theorem decode_encode (message : ServerMessage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) :=
  decodeFramedAllLE_encodeFramedLE 4 4 encodeBody decodeBody message (decodeBody_encodeBody message) (encodeBody_length_lt message) rest

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
  rw [decodeAll_encodeMany ServerMessage.encode ServerMessage.decode ServerMessage.decode_encode ServerMessage.encode_length_pos message.serverMessage _ (encodeMany_length_ge ServerMessage.encode ServerMessage.encode_length_pos message.serverMessage), some_bind]
  rfl

end ServerPacket

end Omi.EurexT7XtiFbeV80Server
