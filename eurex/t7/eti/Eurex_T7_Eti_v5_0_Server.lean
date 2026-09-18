import Omi.Wire

/-!
# Eurex Exchange Enhanced Trading Interface v5.0

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Add Complex Instrument Response is not framed: its length Body Len is not an integer it reads.

Note: Add Flexible Instrument Response is not framed: its length Body Len is not an integer it reads.

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

Note: Alignment Padding pads to a 8 byte boundary: it is read as the bytes left to the end of the frame, fewer than 8, and the frame's length is trusted to keep the boundary.

Note: Forced Logout Notification is not framed: its length Body Len is not an integer it reads.

Note: Alignment Padding pads to a 8 byte boundary: it is read as the bytes left to the end of the frame, fewer than 8, and the frame's length is trusted to keep the boundary.

Note: Forced User Logout Notification is not framed: its length Body Len is not an integer it reads.

Note: Gateway Response is not framed: its length Body Len is not an integer it reads.

Note: Heartbeat Notification is not framed: its length Body Len is not an integer it reads.

Note: Inquire Enrichment Rule Id List Response is not framed: its length Body Len is not an integer it reads.

Note: Inquire Mm Parameter Response is not framed: its length Body Len is not an integer it reads.

Note: Inquire Session List Response is not framed: its length Body Len is not an integer it reads.

Note: Inquire User Response is not framed: its length Body Len is not an integer it reads.

Note: Alignment Padding pads to a 8 byte boundary: it is read as the bytes left to the end of the frame, fewer than 8, and the frame's length is trusted to keep the boundary.

Note: Legal Notification Broadcast is not framed: its length Body Len is not an integer it reads.

Note: Logon Response is not framed: its length Body Len is not an integer it reads.

Note: Logout Response is not framed: its length Body Len is not an integer it reads.

Note: Mm Parameter Definition Response is not framed: its length Body Len is not an integer it reads.

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

Note: Rfq Response is not framed: its length Body Len is not an integer it reads.

Note: Alignment Padding pads to a 8 byte boundary: it is read as the bytes left to the end of the frame, fewer than 8, and the frame's length is trusted to keep the boundary.

Note: Reject is not framed: its length Body Len is not an integer it reads.

Note: Retransmit Me Message Response is not framed: its length Body Len is not an integer it reads.

Note: Retransmit Response is not framed: its length Body Len is not an integer it reads.

Note: Risk Notification Broadcast is not framed: its length Body Len is not an integer it reads.

Note: Service Availability Broadcast is not framed: its length Body Len is not an integer it reads.

Note: Subscribe Response is not framed: its length Body Len is not an integer it reads.

Note: Tes Approve Broadcast is not framed: its length Body Len is not an integer it reads.

Note: Tes Broadcast is not framed: its length Body Len is not an integer it reads.

Note: Tes Delete Broadcast is not framed: its length Body Len is not an integer it reads.

Note: Tes Execution Broadcast is not framed: its length Body Len is not an integer it reads.

Note: Tes Response is not framed: its length Body Len is not an integer it reads.

Note: Tes Trade Broadcast is not framed: its length Body Len is not an integer it reads.

Note: Tes Trading Session Status Broadcast is not framed: its length Body Len is not an integer it reads.

Note: Tes Upload Broadcast is not framed: its length Body Len is not an integer it reads.

Note: Tm Trading Session Status Broadcast is not framed: its length Body Len is not an integer it reads.

Note: Throttle Update Notification is not framed: its length Body Len is not an integer it reads.

Note: Trade Broadcast is not framed: its length Body Len is not an integer it reads.

Note: Trading Session Status Broadcast is not framed: its length Body Len is not an integer it reads.

Note: Unsubscribe Response is not framed: its length Body Len is not an integer it reads.

Note: User Login Response is not framed: its length Body Len is not an integer it reads.

Note: User Logout Response is not framed: its length Body Len is not an integer it reads.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.EurexT7EtiFbeV50Server

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

/-- Message Event Source: one byte code -/
def MessageEventSource.codes : List UInt8 :=
  [0x49, 0x41]

inductive MessageEventSource where
  | broadcasttoInitiator -- Broadcastto Initiator
  | broadcasttoApprover -- Broadcastto Approver
  | unlisted (byte : { byte : UInt8 // byte ∉ MessageEventSource.codes }) -- any other code, kept as it is
  deriving DecidableEq, Repr

namespace MessageEventSource

def toByte : MessageEventSource → UInt8
  | .broadcasttoInitiator => 0x49
  | .broadcasttoApprover => 0x41
  | .unlisted byte => byte.val

/-- The constructor of a listed code -/
def listed (byte : UInt8) : MessageEventSource :=
  if byte = 0x49 then .broadcasttoInitiator
  else .broadcasttoApprover

def ofByte (byte : UInt8) : MessageEventSource :=
  if known : byte ∈ codes then listed byte else .unlisted ⟨byte, known⟩

theorem ofByte_toByte (value : MessageEventSource) : ofByte value.toByte = value := by
  cases value with
  | broadcasttoInitiator => decide
  | broadcasttoApprover => decide
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

/-- Nr Response Header Me Comp: 56 bytes -/
structure NrResponseHeaderMeComp where
  requestTime : BitVec 64
  requestOut : BitVec 64
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
    ++ (encodeUIntLE 8 message.requestOut
    ++ (encodeUIntLE 8 message.trdRegTsTimeIn
    ++ (encodeUIntLE 8 message.trdRegTsTimeOut
    ++ (encodeUIntLE 8 message.responseIn
    ++ (encodeUIntLE 8 message.sendingTime
    ++ (encodeUIntLE 4 message.msgSeqNum
    ++ (encodeUInt 1 message.lastFragment
    ++ (Alpha.encode message.pad3))))))))

def decode (bytes : List UInt8) : Option (NrResponseHeaderMeComp × List UInt8) := do
  let (requestTime, bytes) ← decodeUIntLE 8 bytes
  let (requestOut, bytes) ← decodeUIntLE 8 bytes
  let (trdRegTsTimeIn, bytes) ← decodeUIntLE 8 bytes
  let (trdRegTsTimeOut, bytes) ← decodeUIntLE 8 bytes
  let (responseIn, bytes) ← decodeUIntLE 8 bytes
  let (sendingTime, bytes) ← decodeUIntLE 8 bytes
  let (msgSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (lastFragment, bytes) ← decodeUInt 1 bytes
  let (pad3, bytes) ← Alpha.decode 3 bytes
  pure ({ requestTime, requestOut, trdRegTsTimeIn, trdRegTsTimeOut, responseIn, sendingTime, msgSeqNum, lastFragment, pad3 }, bytes)

@[simp] theorem encode_length (message : NrResponseHeaderMeComp) : (encode message).length = 56 := by
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
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

/-- Add Complex Instrument Response -/
structure AddComplexInstrumentResponse where
  pad2 : Alpha 2
  nrResponseHeaderMeComp : NrResponseHeaderMeComp
  lowLimitPrice : BitVec 64
  highLimitPrice : BitVec 64
  securityId : BitVec 64
  lastUpdateTime : BitVec 64
  securityResponseId : BitVec 64
  marketSegmentId : BitVec 32
  numberOfSecurities : BitVec 32
  securitySubType : BitVec 32
  multilegModel : BitVec 8
  impliedMarketIndicator : BitVec 8
  productComplex : BitVec 8
  instrmtLegGrpComp : Bounded 1 InstrmtLegGrpComp
  deriving DecidableEq, Repr

namespace AddComplexInstrumentResponse

def encode (message : AddComplexInstrumentResponse) : List UInt8 :=
  Alpha.encode message.pad2
    ++ (NrResponseHeaderMeComp.encode message.nrResponseHeaderMeComp
    ++ (encodeUIntLE 8 message.lowLimitPrice
    ++ (encodeUIntLE 8 message.highLimitPrice
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.lastUpdateTime
    ++ (encodeUIntLE 8 message.securityResponseId
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.numberOfSecurities
    ++ (encodeUIntLE 4 message.securitySubType
    ++ (encodeUInt 1 message.multilegModel
    ++ (encodeUInt 1 message.impliedMarketIndicator
    ++ (encodeUInt 1 message.productComplex
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.instrmtLegGrpComp.val.length)
    ++ (encodeMany InstrmtLegGrpComp.encode message.instrmtLegGrpComp.val))))))))))))))

def decode (bytes : List UInt8) : Option (AddComplexInstrumentResponse × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (nrResponseHeaderMeComp, bytes) ← NrResponseHeaderMeComp.decode bytes
  let (lowLimitPrice, bytes) ← decodeUIntLE 8 bytes
  let (highLimitPrice, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (lastUpdateTime, bytes) ← decodeUIntLE 8 bytes
  let (securityResponseId, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (numberOfSecurities, bytes) ← decodeUIntLE 4 bytes
  let (securitySubType, bytes) ← decodeUIntLE 4 bytes
  let (multilegModel, bytes) ← decodeUInt 1 bytes
  let (impliedMarketIndicator, bytes) ← decodeUInt 1 bytes
  let (productComplex, bytes) ← decodeUInt 1 bytes
  let (noLegs, bytes) ← decodeUInt 1 bytes
  let (instrmtLegGrpComp_, bytes) ← decodeMany InstrmtLegGrpComp.decode noLegs.toNat bytes
  if fits_instrmtLegGrpComp : instrmtLegGrpComp_.length < 256 ^ 1 then
    pure ({ pad2, nrResponseHeaderMeComp, lowLimitPrice, highLimitPrice, securityId, lastUpdateTime, securityResponseId, marketSegmentId, numberOfSecurities, securitySubType, multilegModel, impliedMarketIndicator, productComplex, instrmtLegGrpComp := ⟨instrmtLegGrpComp_, fits_instrmtLegGrpComp⟩ }, bytes)
  else none

theorem encode_length_pos (message : AddComplexInstrumentResponse) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : AddComplexInstrumentResponse) : (encode message).length ≤ 8274 := by
  have bound_instrmtLegGrpComp := message.instrmtLegGrpComp.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, NrResponseHeaderMeComp.encode_length, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const InstrmtLegGrpComp.encode 32 InstrmtLegGrpComp.encode_length]
  omega

@[simp] theorem decode_encode (message : AddComplexInstrumentResponse) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 InstrmtLegGrpComp.encode InstrmtLegGrpComp.decode InstrmtLegGrpComp.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.instrmtLegGrpComp.length_lt]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : AddComplexInstrumentResponse) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end AddComplexInstrumentResponse

/-- Add Flexible Instrument Response: 106 bytes -/
structure AddFlexibleInstrumentResponse where
  pad2 : Alpha 2
  nrResponseHeaderMeComp : NrResponseHeaderMeComp
  securityResponseId : BitVec 64
  securityId : BitVec 64
  strikePrice : BitVec 64
  marketSegmentId : BitVec 32
  maturityDate : BitVec 32
  productComplex : BitVec 8
  settlMethod : SettlMethod
  optAttribute : BitVec 8
  putOrCall : BitVec 8
  exerciseStyle : BitVec 8
  symbol : Alpha 4
  pad7 : Alpha 7
  deriving DecidableEq, Repr

namespace AddFlexibleInstrumentResponse

def encode (message : AddFlexibleInstrumentResponse) : List UInt8 :=
  Alpha.encode message.pad2
    ++ (NrResponseHeaderMeComp.encode message.nrResponseHeaderMeComp
    ++ (encodeUIntLE 8 message.securityResponseId
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.strikePrice
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.maturityDate
    ++ (encodeUInt 1 message.productComplex
    ++ (SettlMethod.encode message.settlMethod
    ++ (encodeUInt 1 message.optAttribute
    ++ (encodeUInt 1 message.putOrCall
    ++ (encodeUInt 1 message.exerciseStyle
    ++ (Alpha.encode message.symbol
    ++ (Alpha.encode message.pad7)))))))))))))

def decode (bytes : List UInt8) : Option (AddFlexibleInstrumentResponse × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (nrResponseHeaderMeComp, bytes) ← NrResponseHeaderMeComp.decode bytes
  let (securityResponseId, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (strikePrice, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (maturityDate, bytes) ← decodeUIntLE 4 bytes
  let (productComplex, bytes) ← decodeUInt 1 bytes
  let (settlMethod, bytes) ← SettlMethod.decode bytes
  let (optAttribute, bytes) ← decodeUInt 1 bytes
  let (putOrCall, bytes) ← decodeUInt 1 bytes
  let (exerciseStyle, bytes) ← decodeUInt 1 bytes
  let (symbol, bytes) ← Alpha.decode 4 bytes
  let (pad7, bytes) ← Alpha.decode 7 bytes
  pure ({ pad2, nrResponseHeaderMeComp, securityResponseId, securityId, strikePrice, marketSegmentId, maturityDate, productComplex, settlMethod, optAttribute, putOrCall, exerciseStyle, symbol, pad7 }, bytes)

@[simp] theorem encode_length (message : AddFlexibleInstrumentResponse) : (encode message).length = 106 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, NrResponseHeaderMeComp.encode_length, encodeUIntLE_length, encodeUInt_length, SettlMethod.encode_length]

theorem encode_length_pos (message : AddFlexibleInstrumentResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : AddFlexibleInstrumentResponse) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : AddFlexibleInstrumentResponse) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end AddFlexibleInstrumentResponse

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

/-- Cross Request Response: 66 bytes -/
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

@[simp] theorem encode_length (message : CrossRequestResponse) : (encode message).length = 66 := by
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
  pad2v2 : Alpha 2
  notAffectedOrdersGrpComp : Bounded 2 NotAffectedOrdersGrpComp
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
    ++ (encodeUInt 1 message.partyIdEnteringFirm
    ++ (encodeUInt 1 message.massActionReason
    ++ (encodeUInt 1 message.execInst
    ++ (encodeUInt 1 message.side
    ++ (Alpha.encode message.pad2v2
    ++ (encodeMany NotAffectedOrdersGrpComp.encode message.notAffectedOrdersGrpComp.val)))))))))))))))

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
  let (partyIdEnteringFirm, bytes) ← decodeUInt 1 bytes
  let (massActionReason, bytes) ← decodeUInt 1 bytes
  let (execInst, bytes) ← decodeUInt 1 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (pad2v2, bytes) ← Alpha.decode 2 bytes
  let (notAffectedOrdersGrpComp_, bytes) ← decodeMany NotAffectedOrdersGrpComp.decode noNotAffectedOrders.toNat bytes
  if fits_notAffectedOrdersGrpComp : notAffectedOrdersGrpComp_.length < 256 ^ 2 then
    pure ({ pad2, rbcHeaderMeComp, massActionReportId, securityId, price, marketSegmentId, targetPartyIdSessionId, targetPartyIdExecutingTrader, partyIdEnteringTrader, partyIdEnteringFirm, massActionReason, execInst, side, pad2v2, notAffectedOrdersGrpComp := ⟨notAffectedOrdersGrpComp_, fits_notAffectedOrdersGrpComp⟩ }, bytes)
  else none

theorem encode_length_pos (message : DeleteAllOrderBroadcast) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : DeleteAllOrderBroadcast) : (encode message).length ≤ 1048666 := by
  have bound_notAffectedOrdersGrpComp := message.notAffectedOrdersGrpComp.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, RbcHeaderMeComp.encode_length, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const NotAffectedOrdersGrpComp.encode 16 NotAffectedOrdersGrpComp.encode_length]
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
  rw [decodeMany_bounded 2 NotAffectedOrdersGrpComp.encode NotAffectedOrdersGrpComp.decode NotAffectedOrdersGrpComp.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.notAffectedOrdersGrpComp.length_lt]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : DeleteAllOrderBroadcast) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end DeleteAllOrderBroadcast

/-- Delete All Order Nr Response: 66 bytes -/
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

@[simp] theorem encode_length (message : DeleteAllOrderNrResponse) : (encode message).length = 66 := by
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

/-- Response Header Me Comp: 72 bytes -/
structure ResponseHeaderMeComp where
  requestTime : BitVec 64
  requestOut : BitVec 64
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
    ++ (encodeUIntLE 8 message.requestOut
    ++ (encodeUIntLE 8 message.trdRegTsTimeIn
    ++ (encodeUIntLE 8 message.trdRegTsTimeOut
    ++ (encodeUIntLE 8 message.responseIn
    ++ (encodeUIntLE 8 message.sendingTime
    ++ (encodeUIntLE 4 message.msgSeqNum
    ++ (encodeUIntLE 2 message.partitionId
    ++ (encodeUInt 1 message.applId
    ++ (Alpha.encode message.applMsgId
    ++ (encodeUInt 1 message.lastFragment))))))))))

def decode (bytes : List UInt8) : Option (ResponseHeaderMeComp × List UInt8) := do
  let (requestTime, bytes) ← decodeUIntLE 8 bytes
  let (requestOut, bytes) ← decodeUIntLE 8 bytes
  let (trdRegTsTimeIn, bytes) ← decodeUIntLE 8 bytes
  let (trdRegTsTimeOut, bytes) ← decodeUIntLE 8 bytes
  let (responseIn, bytes) ← decodeUIntLE 8 bytes
  let (sendingTime, bytes) ← decodeUIntLE 8 bytes
  let (msgSeqNum, bytes) ← decodeUIntLE 4 bytes
  let (partitionId, bytes) ← decodeUIntLE 2 bytes
  let (applId, bytes) ← decodeUInt 1 bytes
  let (applMsgId, bytes) ← Alpha.decode 16 bytes
  let (lastFragment, bytes) ← decodeUInt 1 bytes
  pure ({ requestTime, requestOut, trdRegTsTimeIn, trdRegTsTimeOut, responseIn, sendingTime, msgSeqNum, partitionId, applId, applMsgId, lastFragment }, bytes)

@[simp] theorem encode_length (message : ResponseHeaderMeComp) : (encode message).length = 72 := by
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
  pad6 : Alpha 6
  notAffectedOrdersGrpComp : Bounded 2 NotAffectedOrdersGrpComp
  deriving DecidableEq, Repr

namespace DeleteAllOrderResponse

def encode (message : DeleteAllOrderResponse) : List UInt8 :=
  Alpha.encode message.pad2
    ++ (ResponseHeaderMeComp.encode message.responseHeaderMeComp
    ++ (encodeUIntLE 8 message.massActionReportId
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.notAffectedOrdersGrpComp.val.length)
    ++ (Alpha.encode message.pad6
    ++ (encodeMany NotAffectedOrdersGrpComp.encode message.notAffectedOrdersGrpComp.val)))))

def decode (bytes : List UInt8) : Option (DeleteAllOrderResponse × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (responseHeaderMeComp, bytes) ← ResponseHeaderMeComp.decode bytes
  let (massActionReportId, bytes) ← decodeUIntLE 8 bytes
  let (noNotAffectedOrders, bytes) ← decodeUIntLE 2 bytes
  let (pad6, bytes) ← Alpha.decode 6 bytes
  let (notAffectedOrdersGrpComp_, bytes) ← decodeMany NotAffectedOrdersGrpComp.decode noNotAffectedOrders.toNat bytes
  if fits_notAffectedOrdersGrpComp : notAffectedOrdersGrpComp_.length < 256 ^ 2 then
    pure ({ pad2, responseHeaderMeComp, massActionReportId, pad6, notAffectedOrdersGrpComp := ⟨notAffectedOrdersGrpComp_, fits_notAffectedOrdersGrpComp⟩ }, bytes)
  else none

theorem encode_length_pos (message : DeleteAllOrderResponse) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : DeleteAllOrderResponse) : (encode message).length ≤ 1048650 := by
  have bound_notAffectedOrdersGrpComp := message.notAffectedOrdersGrpComp.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, ResponseHeaderMeComp.encode_length, encodeUIntLE_length, encodeMany_length_const NotAffectedOrdersGrpComp.encode 16 NotAffectedOrdersGrpComp.encode_length]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 NotAffectedOrdersGrpComp.encode NotAffectedOrdersGrpComp.decode NotAffectedOrdersGrpComp.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.notAffectedOrdersGrpComp.length_lt]
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
theorem encode_length_le (message : DeleteAllQuoteResponse) : (encode message).length ≤ 524354 := by
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

/-- Delete Order Broadcast: 122 bytes -/
structure DeleteOrderBroadcast where
  pad2 : Alpha 2
  rbcHeaderMeComp : RbcHeaderMeComp
  orderId : BitVec 64
  clOrdId : BitVec 64
  origClOrdId : BitVec 64
  securityId : BitVec 64
  execId : BitVec 64
  cumQty : BitVec 32
  cxlQty : BitVec 32
  marketSegmentId : BitVec 32
  partyIdEnteringTrader : BitVec 32
  execRestatementReason : BitVec 16
  partyIdEnteringFirm : BitVec 8
  ordStatus : OrdStatus
  execType : ExecType
  productComplex : BitVec 8
  side : BitVec 8
  pad1 : Alpha 1
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
    ++ (encodeUIntLE 4 message.cumQty
    ++ (encodeUIntLE 4 message.cxlQty
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.partyIdEnteringTrader
    ++ (encodeUIntLE 2 message.execRestatementReason
    ++ (encodeUInt 1 message.partyIdEnteringFirm
    ++ (OrdStatus.encode message.ordStatus
    ++ (ExecType.encode message.execType
    ++ (encodeUInt 1 message.productComplex
    ++ (encodeUInt 1 message.side
    ++ (Alpha.encode message.pad1)))))))))))))))))

def decode (bytes : List UInt8) : Option (DeleteOrderBroadcast × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderMeComp, bytes) ← RbcHeaderMeComp.decode bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (origClOrdId, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  let (cumQty, bytes) ← decodeUIntLE 4 bytes
  let (cxlQty, bytes) ← decodeUIntLE 4 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (partyIdEnteringTrader, bytes) ← decodeUIntLE 4 bytes
  let (execRestatementReason, bytes) ← decodeUIntLE 2 bytes
  let (partyIdEnteringFirm, bytes) ← decodeUInt 1 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (productComplex, bytes) ← decodeUInt 1 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (pad1, bytes) ← Alpha.decode 1 bytes
  pure ({ pad2, rbcHeaderMeComp, orderId, clOrdId, origClOrdId, securityId, execId, cumQty, cxlQty, marketSegmentId, partyIdEnteringTrader, execRestatementReason, partyIdEnteringFirm, ordStatus, execType, productComplex, side, pad1 }, bytes)

@[simp] theorem encode_length (message : DeleteOrderBroadcast) : (encode message).length = 122 := by
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
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : DeleteOrderBroadcast) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

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
  cumQty : BitVec 32
  cxlQty : BitVec 32
  ordStatus : OrdStatus
  execType : ExecType
  execRestatementReason : BitVec 16
  productComplex : BitVec 8
  pad3 : Alpha 3
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
    ++ (encodeUIntLE 4 message.cumQty
    ++ (encodeUIntLE 4 message.cxlQty
    ++ (OrdStatus.encode message.ordStatus
    ++ (ExecType.encode message.execType
    ++ (encodeUIntLE 2 message.execRestatementReason
    ++ (encodeUInt 1 message.productComplex
    ++ (Alpha.encode message.pad3)))))))))))))

def decode (bytes : List UInt8) : Option (DeleteOrderNrResponse × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (nrResponseHeaderMeComp, bytes) ← NrResponseHeaderMeComp.decode bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (origClOrdId, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  let (cumQty, bytes) ← decodeUIntLE 4 bytes
  let (cxlQty, bytes) ← decodeUIntLE 4 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (execRestatementReason, bytes) ← decodeUIntLE 2 bytes
  let (productComplex, bytes) ← decodeUInt 1 bytes
  let (pad3, bytes) ← Alpha.decode 3 bytes
  pure ({ pad2, nrResponseHeaderMeComp, orderId, clOrdId, origClOrdId, securityId, execId, cumQty, cxlQty, ordStatus, execType, execRestatementReason, productComplex, pad3 }, bytes)

@[simp] theorem encode_length (message : DeleteOrderNrResponse) : (encode message).length = 114 := by
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

/-- Delete Order Response: 130 bytes -/
structure DeleteOrderResponse where
  pad2 : Alpha 2
  responseHeaderMeComp : ResponseHeaderMeComp
  orderId : BitVec 64
  clOrdId : BitVec 64
  origClOrdId : BitVec 64
  securityId : BitVec 64
  execId : BitVec 64
  cumQty : BitVec 32
  cxlQty : BitVec 32
  ordStatus : OrdStatus
  execType : ExecType
  execRestatementReason : BitVec 16
  productComplex : BitVec 8
  pad3 : Alpha 3
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
    ++ (encodeUIntLE 4 message.cumQty
    ++ (encodeUIntLE 4 message.cxlQty
    ++ (OrdStatus.encode message.ordStatus
    ++ (ExecType.encode message.execType
    ++ (encodeUIntLE 2 message.execRestatementReason
    ++ (encodeUInt 1 message.productComplex
    ++ (Alpha.encode message.pad3)))))))))))))

def decode (bytes : List UInt8) : Option (DeleteOrderResponse × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (responseHeaderMeComp, bytes) ← ResponseHeaderMeComp.decode bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (origClOrdId, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  let (cumQty, bytes) ← decodeUIntLE 4 bytes
  let (cxlQty, bytes) ← decodeUIntLE 4 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (execRestatementReason, bytes) ← decodeUIntLE 2 bytes
  let (productComplex, bytes) ← decodeUInt 1 bytes
  let (pad3, bytes) ← Alpha.decode 3 bytes
  pure ({ pad2, responseHeaderMeComp, orderId, clOrdId, origClOrdId, securityId, execId, cumQty, cxlQty, ordStatus, execType, execRestatementReason, productComplex, pad3 }, bytes)

@[simp] theorem encode_length (message : DeleteOrderResponse) : (encode message).length = 130 := by
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

/-- Gateway Response: 50 bytes -/
structure GatewayResponse where
  pad2 : Alpha 2
  responseHeaderComp : ResponseHeaderComp
  gatewayId : BitVec 32
  gatewaySubId : BitVec 32
  secondaryGatewayId : BitVec 32
  secondaryGatewaySubId : BitVec 32
  sessionMode : BitVec 8
  tradSesMode : BitVec 8
  pad6 : Alpha 6
  deriving DecidableEq, Repr

namespace GatewayResponse

def encode (message : GatewayResponse) : List UInt8 :=
  Alpha.encode message.pad2
    ++ (ResponseHeaderComp.encode message.responseHeaderComp
    ++ (encodeUIntLE 4 message.gatewayId
    ++ (encodeUIntLE 4 message.gatewaySubId
    ++ (encodeUIntLE 4 message.secondaryGatewayId
    ++ (encodeUIntLE 4 message.secondaryGatewaySubId
    ++ (encodeUInt 1 message.sessionMode
    ++ (encodeUInt 1 message.tradSesMode
    ++ (Alpha.encode message.pad6))))))))

def decode (bytes : List UInt8) : Option (GatewayResponse × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (responseHeaderComp, bytes) ← ResponseHeaderComp.decode bytes
  let (gatewayId, bytes) ← decodeUIntLE 4 bytes
  let (gatewaySubId, bytes) ← decodeUIntLE 4 bytes
  let (secondaryGatewayId, bytes) ← decodeUIntLE 4 bytes
  let (secondaryGatewaySubId, bytes) ← decodeUIntLE 4 bytes
  let (sessionMode, bytes) ← decodeUInt 1 bytes
  let (tradSesMode, bytes) ← decodeUInt 1 bytes
  let (pad6, bytes) ← Alpha.decode 6 bytes
  pure ({ pad2, responseHeaderComp, gatewayId, gatewaySubId, secondaryGatewayId, secondaryGatewaySubId, sessionMode, tradSesMode, pad6 }, bytes)

@[simp] theorem encode_length (message : GatewayResponse) : (encode message).length = 50 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, ResponseHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length]

theorem encode_length_pos (message : GatewayResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : GatewayResponse) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : GatewayResponse) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end GatewayResponse

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

/-- Enrichment Rules Grp Comp: 64 bytes -/
structure EnrichmentRulesGrpComp where
  enrichmentRuleId : BitVec 16
  partyIdOriginationMarket : BitVec 8
  account : Alpha 2
  positionEffect : PositionEffect
  partyIdTakeUpTradingFirm : Alpha 5
  partyIdOrderOriginationFirm : Alpha 7
  partyIdBeneficiary : Alpha 9
  freeText1 : Alpha 12
  freeText2 : Alpha 12
  freeText3 : Alpha 12
  pad1 : Alpha 1
  deriving DecidableEq, Repr

namespace EnrichmentRulesGrpComp

def encode (message : EnrichmentRulesGrpComp) : List UInt8 :=
  encodeUIntLE 2 message.enrichmentRuleId
    ++ (encodeUInt 1 message.partyIdOriginationMarket
    ++ (Alpha.encode message.account
    ++ (PositionEffect.encode message.positionEffect
    ++ (Alpha.encode message.partyIdTakeUpTradingFirm
    ++ (Alpha.encode message.partyIdOrderOriginationFirm
    ++ (Alpha.encode message.partyIdBeneficiary
    ++ (Alpha.encode message.freeText1
    ++ (Alpha.encode message.freeText2
    ++ (Alpha.encode message.freeText3
    ++ (Alpha.encode message.pad1))))))))))

def decode (bytes : List UInt8) : Option (EnrichmentRulesGrpComp × List UInt8) := do
  let (enrichmentRuleId, bytes) ← decodeUIntLE 2 bytes
  let (partyIdOriginationMarket, bytes) ← decodeUInt 1 bytes
  let (account, bytes) ← Alpha.decode 2 bytes
  let (positionEffect, bytes) ← PositionEffect.decode bytes
  let (partyIdTakeUpTradingFirm, bytes) ← Alpha.decode 5 bytes
  let (partyIdOrderOriginationFirm, bytes) ← Alpha.decode 7 bytes
  let (partyIdBeneficiary, bytes) ← Alpha.decode 9 bytes
  let (freeText1, bytes) ← Alpha.decode 12 bytes
  let (freeText2, bytes) ← Alpha.decode 12 bytes
  let (freeText3, bytes) ← Alpha.decode 12 bytes
  let (pad1, bytes) ← Alpha.decode 1 bytes
  pure ({ enrichmentRuleId, partyIdOriginationMarket, account, positionEffect, partyIdTakeUpTradingFirm, partyIdOrderOriginationFirm, partyIdBeneficiary, freeText1, freeText2, freeText3, pad1 }, bytes)

@[simp] theorem encode_length (message : EnrichmentRulesGrpComp) : (encode message).length = 64 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length, PositionEffect.encode_length]

theorem encode_length_pos (message : EnrichmentRulesGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EnrichmentRulesGrpComp) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
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
theorem encode_length_le (message : InquireEnrichmentRuleIdListResponse) : (encode message).length ≤ 4194290 := by
  have bound_enrichmentRulesGrpComp := message.enrichmentRulesGrpComp.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, ResponseHeaderComp.encode_length, encodeUIntLE_length, encodeMany_length_const EnrichmentRulesGrpComp.encode 64 EnrichmentRulesGrpComp.encode_length]
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

/-- Mm Parameter Grp Comp: 32 bytes -/
structure MmParameterGrpComp where
  exposureDuration : BitVec 64
  cumQty : BitVec 32
  pctCount : BitVec 32
  delta : BitVec 32
  vega : BitVec 32
  productComplex : BitVec 8
  pad7 : Alpha 7
  deriving DecidableEq, Repr

namespace MmParameterGrpComp

def encode (message : MmParameterGrpComp) : List UInt8 :=
  encodeUIntLE 8 message.exposureDuration
    ++ (encodeUIntLE 4 message.cumQty
    ++ (encodeUIntLE 4 message.pctCount
    ++ (encodeUIntLE 4 message.delta
    ++ (encodeUIntLE 4 message.vega
    ++ (encodeUInt 1 message.productComplex
    ++ (Alpha.encode message.pad7))))))

def decode (bytes : List UInt8) : Option (MmParameterGrpComp × List UInt8) := do
  let (exposureDuration, bytes) ← decodeUIntLE 8 bytes
  let (cumQty, bytes) ← decodeUIntLE 4 bytes
  let (pctCount, bytes) ← decodeUIntLE 4 bytes
  let (delta, bytes) ← decodeUIntLE 4 bytes
  let (vega, bytes) ← decodeUIntLE 4 bytes
  let (productComplex, bytes) ← decodeUInt 1 bytes
  let (pad7, bytes) ← Alpha.decode 7 bytes
  pure ({ exposureDuration, cumQty, pctCount, delta, vega, productComplex, pad7 }, bytes)

@[simp] theorem encode_length (message : MmParameterGrpComp) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : MmParameterGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MmParameterGrpComp) (rest : List UInt8) :
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
  rw [Alpha.decode_encode, some_bind]
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
    ++ (NrResponseHeaderMeComp.encode message.nrResponseHeaderMeComp
    ++ (encodeUIntLE 8 message.mmParameterReportId
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.mmParameterGrpComp.val.length)
    ++ (Alpha.encode message.pad3
    ++ (encodeMany MmParameterGrpComp.encode message.mmParameterGrpComp.val))))))

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
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : InquireMmParameterResponse) : (encode message).length ≤ 8234 := by
  have bound_mmParameterGrpComp := message.mmParameterGrpComp.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, NrResponseHeaderMeComp.encode_length, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const MmParameterGrpComp.encode 32 MmParameterGrpComp.encode_length]
  omega

@[simp] theorem decode_encode (message : InquireMmParameterResponse) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 MmParameterGrpComp.encode MmParameterGrpComp.decode MmParameterGrpComp.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.mmParameterGrpComp.length_lt]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : InquireMmParameterResponse) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end InquireMmParameterResponse

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
  pad7 : Alpha 7
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
    ++ (Alpha.encode message.pad7))))))))))

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
  let (pad7, bytes) ← Alpha.decode 7 bytes
  pure ({ pad2, responseHeaderComp, throttleTimeInterval, throttleNoMsgs, throttleDisconnectLimit, heartBtInt, sessionInstanceId, marketId, tradSesMode, defaultCstmApplVerId, pad7 }, bytes)

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

/-- Mm Parameter Definition Response: 66 bytes -/
structure MmParameterDefinitionResponse where
  pad2 : Alpha 2
  nrResponseHeaderMeComp : NrResponseHeaderMeComp
  execId : BitVec 64
  deriving DecidableEq, Repr

namespace MmParameterDefinitionResponse

def encode (message : MmParameterDefinitionResponse) : List UInt8 :=
  Alpha.encode message.pad2
    ++ (NrResponseHeaderMeComp.encode message.nrResponseHeaderMeComp
    ++ (encodeUIntLE 8 message.execId))

def decode (bytes : List UInt8) : Option (MmParameterDefinitionResponse × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (nrResponseHeaderMeComp, bytes) ← NrResponseHeaderMeComp.decode bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  pure ({ pad2, nrResponseHeaderMeComp, execId }, bytes)

@[simp] theorem encode_length (message : MmParameterDefinitionResponse) : (encode message).length = 66 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, NrResponseHeaderMeComp.encode_length, encodeUIntLE_length]

theorem encode_length_pos (message : MmParameterDefinitionResponse) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : MmParameterDefinitionResponse) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, NrResponseHeaderMeComp.decode_encode, some_bind]
  dsimp only
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : MmParameterDefinitionResponse) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end MmParameterDefinitionResponse

/-- Quote Entry Ack Grp Comp: 24 bytes -/
structure QuoteEntryAckGrpComp where
  securityId : BitVec 64
  bidCxlSize : BitVec 32
  offerCxlSize : BitVec 32
  quoteEntryRejectReason : BitVec 32
  quoteEntryStatus : BitVec 8
  pad3 : Alpha 3
  deriving DecidableEq, Repr

namespace QuoteEntryAckGrpComp

def encode (message : QuoteEntryAckGrpComp) : List UInt8 :=
  encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 4 message.bidCxlSize
    ++ (encodeUIntLE 4 message.offerCxlSize
    ++ (encodeUIntLE 4 message.quoteEntryRejectReason
    ++ (encodeUInt 1 message.quoteEntryStatus
    ++ (Alpha.encode message.pad3)))))

def decode (bytes : List UInt8) : Option (QuoteEntryAckGrpComp × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (bidCxlSize, bytes) ← decodeUIntLE 4 bytes
  let (offerCxlSize, bytes) ← decodeUIntLE 4 bytes
  let (quoteEntryRejectReason, bytes) ← decodeUIntLE 4 bytes
  let (quoteEntryStatus, bytes) ← decodeUInt 1 bytes
  let (pad3, bytes) ← Alpha.decode 3 bytes
  pure ({ securityId, bidCxlSize, offerCxlSize, quoteEntryRejectReason, quoteEntryStatus, pad3 }, bytes)

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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
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
  let (noQuoteEntries, bytes) ← decodeUInt 1 bytes
  let (pad3, bytes) ← Alpha.decode 3 bytes
  let (quoteEntryAckGrpComp_, bytes) ← decodeMany QuoteEntryAckGrpComp.decode noQuoteEntries.toNat bytes
  if fits_quoteEntryAckGrpComp : quoteEntryAckGrpComp_.length < 256 ^ 1 then
    pure ({ pad2, nrResponseHeaderMeComp, quoteId, quoteResponseId, marketSegmentId, pad3, quoteEntryAckGrpComp := ⟨quoteEntryAckGrpComp_, fits_quoteEntryAckGrpComp⟩ }, bytes)
  else none

theorem encode_length_pos (message : MassQuoteResponse) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : MassQuoteResponse) : (encode message).length ≤ 6202 := by
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

/-- Modify Order Nr Response: 122 bytes -/
structure ModifyOrderNrResponse where
  pad2 : Alpha 2
  nrResponseHeaderMeComp : NrResponseHeaderMeComp
  orderId : BitVec 64
  clOrdId : BitVec 64
  origClOrdId : BitVec 64
  securityId : BitVec 64
  execId : BitVec 64
  leavesQty : BitVec 32
  cumQty : BitVec 32
  cxlQty : BitVec 32
  ordStatus : OrdStatus
  execType : ExecType
  execRestatementReason : BitVec 16
  crossed : BitVec 8
  productComplex : BitVec 8
  triggered : BitVec 8
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
    ++ (encodeUIntLE 4 message.leavesQty
    ++ (encodeUIntLE 4 message.cumQty
    ++ (encodeUIntLE 4 message.cxlQty
    ++ (OrdStatus.encode message.ordStatus
    ++ (ExecType.encode message.execType
    ++ (encodeUIntLE 2 message.execRestatementReason
    ++ (encodeUInt 1 message.crossed
    ++ (encodeUInt 1 message.productComplex
    ++ (encodeUInt 1 message.triggered
    ++ (Alpha.encode message.pad5))))))))))))))))

def decode (bytes : List UInt8) : Option (ModifyOrderNrResponse × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (nrResponseHeaderMeComp, bytes) ← NrResponseHeaderMeComp.decode bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (origClOrdId, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  let (leavesQty, bytes) ← decodeUIntLE 4 bytes
  let (cumQty, bytes) ← decodeUIntLE 4 bytes
  let (cxlQty, bytes) ← decodeUIntLE 4 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (execRestatementReason, bytes) ← decodeUIntLE 2 bytes
  let (crossed, bytes) ← decodeUInt 1 bytes
  let (productComplex, bytes) ← decodeUInt 1 bytes
  let (triggered, bytes) ← decodeUInt 1 bytes
  let (pad5, bytes) ← Alpha.decode 5 bytes
  pure ({ pad2, nrResponseHeaderMeComp, orderId, clOrdId, origClOrdId, securityId, execId, leavesQty, cumQty, cxlQty, ordStatus, execType, execRestatementReason, crossed, productComplex, triggered, pad5 }, bytes)

@[simp] theorem encode_length (message : ModifyOrderNrResponse) : (encode message).length = 122 := by
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

/-- Modify Order Response: 146 bytes -/
structure ModifyOrderResponse where
  pad2 : Alpha 2
  responseHeaderMeComp : ResponseHeaderMeComp
  orderId : BitVec 64
  clOrdId : BitVec 64
  origClOrdId : BitVec 64
  securityId : BitVec 64
  execId : BitVec 64
  trdRegTsTimePriority : BitVec 64
  leavesQty : BitVec 32
  cumQty : BitVec 32
  cxlQty : BitVec 32
  ordStatus : OrdStatus
  execType : ExecType
  execRestatementReason : BitVec 16
  crossed : BitVec 8
  productComplex : BitVec 8
  triggered : BitVec 8
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
    ++ (encodeUIntLE 8 message.trdRegTsTimePriority
    ++ (encodeUIntLE 4 message.leavesQty
    ++ (encodeUIntLE 4 message.cumQty
    ++ (encodeUIntLE 4 message.cxlQty
    ++ (OrdStatus.encode message.ordStatus
    ++ (ExecType.encode message.execType
    ++ (encodeUIntLE 2 message.execRestatementReason
    ++ (encodeUInt 1 message.crossed
    ++ (encodeUInt 1 message.productComplex
    ++ (encodeUInt 1 message.triggered
    ++ (Alpha.encode message.pad5)))))))))))))))))

def decode (bytes : List UInt8) : Option (ModifyOrderResponse × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (responseHeaderMeComp, bytes) ← ResponseHeaderMeComp.decode bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (origClOrdId, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  let (trdRegTsTimePriority, bytes) ← decodeUIntLE 8 bytes
  let (leavesQty, bytes) ← decodeUIntLE 4 bytes
  let (cumQty, bytes) ← decodeUIntLE 4 bytes
  let (cxlQty, bytes) ← decodeUIntLE 4 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (execRestatementReason, bytes) ← decodeUIntLE 2 bytes
  let (crossed, bytes) ← decodeUInt 1 bytes
  let (productComplex, bytes) ← decodeUInt 1 bytes
  let (triggered, bytes) ← decodeUInt 1 bytes
  let (pad5, bytes) ← Alpha.decode 5 bytes
  pure ({ pad2, responseHeaderMeComp, orderId, clOrdId, origClOrdId, securityId, execId, trdRegTsTimePriority, leavesQty, cumQty, cxlQty, ordStatus, execType, execRestatementReason, crossed, productComplex, triggered, pad5 }, bytes)

@[simp] theorem encode_length (message : ModifyOrderResponse) : (encode message).length = 146 := by
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
  ordStatus : OrdStatus
  execType : ExecType
  execRestatementReason : BitVec 16
  crossed : BitVec 8
  productComplex : BitVec 8
  triggered : BitVec 8
  pad1 : Alpha 1
  deriving DecidableEq, Repr

namespace NewOrderNrResponse

def encode (message : NewOrderNrResponse) : List UInt8 :=
  Alpha.encode message.pad2
    ++ (NrResponseHeaderMeComp.encode message.nrResponseHeaderMeComp
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.execId
    ++ (OrdStatus.encode message.ordStatus
    ++ (ExecType.encode message.execType
    ++ (encodeUIntLE 2 message.execRestatementReason
    ++ (encodeUInt 1 message.crossed
    ++ (encodeUInt 1 message.productComplex
    ++ (encodeUInt 1 message.triggered
    ++ (Alpha.encode message.pad1))))))))))))

def decode (bytes : List UInt8) : Option (NewOrderNrResponse × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (nrResponseHeaderMeComp, bytes) ← NrResponseHeaderMeComp.decode bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (execRestatementReason, bytes) ← decodeUIntLE 2 bytes
  let (crossed, bytes) ← decodeUInt 1 bytes
  let (productComplex, bytes) ← decodeUInt 1 bytes
  let (triggered, bytes) ← decodeUInt 1 bytes
  let (pad1, bytes) ← Alpha.decode 1 bytes
  pure ({ pad2, nrResponseHeaderMeComp, orderId, clOrdId, securityId, execId, ordStatus, execType, execRestatementReason, crossed, productComplex, triggered, pad1 }, bytes)

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
  ordStatus : OrdStatus
  execType : ExecType
  execRestatementReason : BitVec 16
  crossed : BitVec 8
  productComplex : BitVec 8
  triggered : BitVec 8
  pad1 : Alpha 1
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
    ++ (OrdStatus.encode message.ordStatus
    ++ (ExecType.encode message.execType
    ++ (encodeUIntLE 2 message.execRestatementReason
    ++ (encodeUInt 1 message.crossed
    ++ (encodeUInt 1 message.productComplex
    ++ (encodeUInt 1 message.triggered
    ++ (Alpha.encode message.pad1))))))))))))))

def decode (bytes : List UInt8) : Option (NewOrderResponse × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (responseHeaderMeComp, bytes) ← ResponseHeaderMeComp.decode bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  let (trdRegTsEntryTime, bytes) ← decodeUIntLE 8 bytes
  let (trdRegTsTimePriority, bytes) ← decodeUIntLE 8 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (execRestatementReason, bytes) ← decodeUIntLE 2 bytes
  let (crossed, bytes) ← decodeUInt 1 bytes
  let (productComplex, bytes) ← decodeUInt 1 bytes
  let (triggered, bytes) ← decodeUInt 1 bytes
  let (pad1, bytes) ← Alpha.decode 1 bytes
  pure ({ pad2, responseHeaderMeComp, orderId, clOrdId, securityId, execId, trdRegTsEntryTime, trdRegTsTimePriority, ordStatus, execType, execRestatementReason, crossed, productComplex, triggered, pad1 }, bytes)

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

/-- Fills Grp Comp: 24 bytes -/
structure FillsGrpComp where
  fillPx : BitVec 64
  fillQty : BitVec 32
  fillMatchId : BitVec 32
  fillExecId : BitVec 32
  fillLiquidityInd : BitVec 8
  pad3 : Alpha 3
  deriving DecidableEq, Repr

namespace FillsGrpComp

def encode (message : FillsGrpComp) : List UInt8 :=
  encodeUIntLE 8 message.fillPx
    ++ (encodeUIntLE 4 message.fillQty
    ++ (encodeUIntLE 4 message.fillMatchId
    ++ (encodeUIntLE 4 message.fillExecId
    ++ (encodeUInt 1 message.fillLiquidityInd
    ++ (Alpha.encode message.pad3)))))

def decode (bytes : List UInt8) : Option (FillsGrpComp × List UInt8) := do
  let (fillPx, bytes) ← decodeUIntLE 8 bytes
  let (fillQty, bytes) ← decodeUIntLE 4 bytes
  let (fillMatchId, bytes) ← decodeUIntLE 4 bytes
  let (fillExecId, bytes) ← decodeUIntLE 4 bytes
  let (fillLiquidityInd, bytes) ← decodeUInt 1 bytes
  let (pad3, bytes) ← Alpha.decode 3 bytes
  pure ({ fillPx, fillQty, fillMatchId, fillExecId, fillLiquidityInd, pad3 }, bytes)

@[simp] theorem encode_length (message : FillsGrpComp) : (encode message).length = 24 := by
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

/-- Instrmnt Leg Exec Grp Comp: 32 bytes -/
structure InstrmntLegExecGrpComp where
  legSecurityId : BitVec 64
  legLastPx : BitVec 64
  legLastQty : BitVec 32
  legExecId : BitVec 32
  legSide : BitVec 8
  fillRefId : BitVec 8
  pad6 : Alpha 6
  deriving DecidableEq, Repr

namespace InstrmntLegExecGrpComp

def encode (message : InstrmntLegExecGrpComp) : List UInt8 :=
  encodeUIntLE 8 message.legSecurityId
    ++ (encodeUIntLE 8 message.legLastPx
    ++ (encodeUIntLE 4 message.legLastQty
    ++ (encodeUIntLE 4 message.legExecId
    ++ (encodeUInt 1 message.legSide
    ++ (encodeUInt 1 message.fillRefId
    ++ (Alpha.encode message.pad6))))))

def decode (bytes : List UInt8) : Option (InstrmntLegExecGrpComp × List UInt8) := do
  let (legSecurityId, bytes) ← decodeUIntLE 8 bytes
  let (legLastPx, bytes) ← decodeUIntLE 8 bytes
  let (legLastQty, bytes) ← decodeUIntLE 4 bytes
  let (legExecId, bytes) ← decodeUIntLE 4 bytes
  let (legSide, bytes) ← decodeUInt 1 bytes
  let (fillRefId, bytes) ← decodeUInt 1 bytes
  let (pad6, bytes) ← Alpha.decode 6 bytes
  pure ({ legSecurityId, legLastPx, legLastQty, legExecId, legSide, fillRefId, pad6 }, bytes)

@[simp] theorem encode_length (message : InstrmntLegExecGrpComp) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : InstrmntLegExecGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstrmntLegExecGrpComp) (rest : List UInt8) :
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

end InstrmntLegExecGrpComp

/-- Order Exec Notification -/
structure OrderExecNotification where
  pad2 : Alpha 2
  rbcHeaderMeComp : RbcHeaderMeComp
  orderId : BitVec 64
  clOrdId : BitVec 64
  origClOrdId : BitVec 64
  securityId : BitVec 64
  execId : BitVec 64
  marketSegmentId : BitVec 32
  leavesQty : BitVec 32
  cumQty : BitVec 32
  cxlQty : BitVec 32
  execRestatementReason : BitVec 16
  side : BitVec 8
  productComplex : BitVec 8
  ordStatus : OrdStatus
  execType : ExecType
  triggered : BitVec 8
  crossed : BitVec 8
  pad5 : Alpha 5
  fillsGrpComp : Bounded 1 FillsGrpComp
  instrmntLegExecGrpComp : Bounded 2 InstrmntLegExecGrpComp
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
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.leavesQty
    ++ (encodeUIntLE 4 message.cumQty
    ++ (encodeUIntLE 4 message.cxlQty
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.instrmntLegExecGrpComp.val.length)
    ++ (encodeUIntLE 2 message.execRestatementReason
    ++ (encodeUInt 1 message.side
    ++ (encodeUInt 1 message.productComplex
    ++ (OrdStatus.encode message.ordStatus
    ++ (ExecType.encode message.execType
    ++ (encodeUInt 1 message.triggered
    ++ (encodeUInt 1 message.crossed
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.fillsGrpComp.val.length)
    ++ (Alpha.encode message.pad5
    ++ (encodeMany FillsGrpComp.encode message.fillsGrpComp.val
    ++ (encodeMany InstrmntLegExecGrpComp.encode message.instrmntLegExecGrpComp.val))))))))))))))))))))))

def decode (bytes : List UInt8) : Option (OrderExecNotification × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderMeComp, bytes) ← RbcHeaderMeComp.decode bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (origClOrdId, bytes) ← decodeUIntLE 8 bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (execId, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (leavesQty, bytes) ← decodeUIntLE 4 bytes
  let (cumQty, bytes) ← decodeUIntLE 4 bytes
  let (cxlQty, bytes) ← decodeUIntLE 4 bytes
  let (noLegExecs, bytes) ← decodeUIntLE 2 bytes
  let (execRestatementReason, bytes) ← decodeUIntLE 2 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (productComplex, bytes) ← decodeUInt 1 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (triggered, bytes) ← decodeUInt 1 bytes
  let (crossed, bytes) ← decodeUInt 1 bytes
  let (noFills, bytes) ← decodeUInt 1 bytes
  let (pad5, bytes) ← Alpha.decode 5 bytes
  let (fillsGrpComp_, bytes) ← decodeMany FillsGrpComp.decode noFills.toNat bytes
  let (instrmntLegExecGrpComp_, bytes) ← decodeMany InstrmntLegExecGrpComp.decode noLegExecs.toNat bytes
  if fits_fillsGrpComp : fillsGrpComp_.length < 256 ^ 1 then
    if fits_instrmntLegExecGrpComp : instrmntLegExecGrpComp_.length < 256 ^ 2 then
      pure ({ pad2, rbcHeaderMeComp, orderId, clOrdId, origClOrdId, securityId, execId, marketSegmentId, leavesQty, cumQty, cxlQty, execRestatementReason, side, productComplex, ordStatus, execType, triggered, crossed, pad5, fillsGrpComp := ⟨fillsGrpComp_, fits_fillsGrpComp⟩, instrmntLegExecGrpComp := ⟨instrmntLegExecGrpComp_, fits_instrmntLegExecGrpComp⟩ }, bytes)
    else none
  else none

theorem encode_length_pos (message : OrderExecNotification) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : OrderExecNotification) : (encode message).length ≤ 2103370 := by
  have bound_fillsGrpComp := message.fillsGrpComp.length_lt
  have bound_instrmntLegExecGrpComp := message.instrmntLegExecGrpComp.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, RbcHeaderMeComp.encode_length, encodeUIntLE_length, encodeUInt_length, OrdStatus.encode_length, ExecType.encode_length, encodeMany_length_const FillsGrpComp.encode 24 FillsGrpComp.encode_length, encodeMany_length_const InstrmntLegExecGrpComp.encode 32 InstrmntLegExecGrpComp.encode_length]
  omega

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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeMany_bounded 1 FillsGrpComp.encode FillsGrpComp.decode FillsGrpComp.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 InstrmntLegExecGrpComp.encode InstrmntLegExecGrpComp.decode InstrmntLegExecGrpComp.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.fillsGrpComp.length_lt, dite_eq_left message.instrmntLegExecGrpComp.length_lt]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : OrderExecNotification) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

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
  stopPx : BitVec 64
  marketSegmentId : BitVec 32
  leavesQty : BitVec 32
  cumQty : BitVec 32
  cxlQty : BitVec 32
  orderQty : BitVec 32
  expireDate : BitVec 32
  matchInstCrossId : BitVec 32
  partyIdExecutingUnit : BitVec 32
  partyIdSessionId : BitVec 32
  partyIdExecutingTrader : BitVec 32
  partyIdEnteringTrader : BitVec 32
  execRestatementReason : BitVec 16
  partyIdEnteringFirm : BitVec 8
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
  custOrderHandlingInst : Alpha 1
  complianceText : Alpha 20
  freeText1 : Alpha 12
  freeText2 : Alpha 12
  freeText3 : Alpha 12
  triggered : BitVec 8
  crossed : BitVec 8
  pad6 : Alpha 6
  legOrdGrpComp : Bounded 1 LegOrdGrpComp
  fillsGrpComp : Bounded 1 FillsGrpComp
  instrmntLegExecGrpComp : Bounded 2 InstrmntLegExecGrpComp
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
    ++ (encodeUIntLE 8 message.stopPx
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.leavesQty
    ++ (encodeUIntLE 4 message.cumQty
    ++ (encodeUIntLE 4 message.cxlQty
    ++ (encodeUIntLE 4 message.orderQty
    ++ (encodeUIntLE 4 message.expireDate
    ++ (encodeUIntLE 4 message.matchInstCrossId
    ++ (encodeUIntLE 4 message.partyIdExecutingUnit
    ++ (encodeUIntLE 4 message.partyIdSessionId
    ++ (encodeUIntLE 4 message.partyIdExecutingTrader
    ++ (encodeUIntLE 4 message.partyIdEnteringTrader
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.instrmntLegExecGrpComp.val.length)
    ++ (encodeUIntLE 2 message.execRestatementReason
    ++ (encodeUInt 1 message.partyIdEnteringFirm
    ++ (encodeUInt 1 message.productComplex
    ++ (OrdStatus.encode message.ordStatus
    ++ (ExecType.encode message.execType
    ++ (encodeUInt 1 message.side
    ++ (encodeUInt 1 message.ordType
    ++ (encodeUInt 1 message.tradingCapacity
    ++ (encodeUInt 1 message.timeInForce
    ++ (encodeUInt 1 message.execInst
    ++ (encodeUInt 1 message.tradingSessionSubId
    ++ (encodeUInt 1 message.applSeqIndicator
    ++ (Alpha.encode message.account
    ++ (Alpha.encode message.partyIdPositionAccount
    ++ (PositionEffect.encode message.positionEffect
    ++ (Alpha.encode message.partyIdTakeUpTradingFirm
    ++ (Alpha.encode message.partyIdOrderOriginationFirm
    ++ (Alpha.encode message.partyIdBeneficiary
    ++ (Alpha.encode message.partyIdLocationId
    ++ (Alpha.encode message.custOrderHandlingInst
    ++ (Alpha.encode message.complianceText
    ++ (Alpha.encode message.freeText1
    ++ (Alpha.encode message.freeText2
    ++ (Alpha.encode message.freeText3
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.fillsGrpComp.val.length)
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.legOrdGrpComp.val.length)
    ++ (encodeUInt 1 message.triggered
    ++ (encodeUInt 1 message.crossed
    ++ (Alpha.encode message.pad6
    ++ (encodeMany LegOrdGrpComp.encode message.legOrdGrpComp.val
    ++ (encodeMany FillsGrpComp.encode message.fillsGrpComp.val
    ++ (encodeMany InstrmntLegExecGrpComp.encode message.instrmntLegExecGrpComp.val))))))))))))))))))))))))))))))))))))))))))))))))))))))

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
  let (stopPx, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (leavesQty, bytes) ← decodeUIntLE 4 bytes
  let (cumQty, bytes) ← decodeUIntLE 4 bytes
  let (cxlQty, bytes) ← decodeUIntLE 4 bytes
  let (orderQty, bytes) ← decodeUIntLE 4 bytes
  let (expireDate, bytes) ← decodeUIntLE 4 bytes
  let (matchInstCrossId, bytes) ← decodeUIntLE 4 bytes
  let (partyIdExecutingUnit, bytes) ← decodeUIntLE 4 bytes
  let (partyIdSessionId, bytes) ← decodeUIntLE 4 bytes
  let (partyIdExecutingTrader, bytes) ← decodeUIntLE 4 bytes
  let (partyIdEnteringTrader, bytes) ← decodeUIntLE 4 bytes
  let (noLegExecs, bytes) ← decodeUIntLE 2 bytes
  let (execRestatementReason, bytes) ← decodeUIntLE 2 bytes
  let (partyIdEnteringFirm, bytes) ← decodeUInt 1 bytes
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
  let (custOrderHandlingInst, bytes) ← Alpha.decode 1 bytes
  let (complianceText, bytes) ← Alpha.decode 20 bytes
  let (freeText1, bytes) ← Alpha.decode 12 bytes
  let (freeText2, bytes) ← Alpha.decode 12 bytes
  let (freeText3, bytes) ← Alpha.decode 12 bytes
  let (noFills, bytes) ← decodeUInt 1 bytes
  let (noLegs, bytes) ← decodeUInt 1 bytes
  let (triggered, bytes) ← decodeUInt 1 bytes
  let (crossed, bytes) ← decodeUInt 1 bytes
  let (pad6, bytes) ← Alpha.decode 6 bytes
  let (legOrdGrpComp_, bytes) ← decodeMany LegOrdGrpComp.decode noLegs.toNat bytes
  let (fillsGrpComp_, bytes) ← decodeMany FillsGrpComp.decode noFills.toNat bytes
  let (instrmntLegExecGrpComp_, bytes) ← decodeMany InstrmntLegExecGrpComp.decode noLegExecs.toNat bytes
  if fits_legOrdGrpComp : legOrdGrpComp_.length < 256 ^ 1 then
    if fits_fillsGrpComp : fillsGrpComp_.length < 256 ^ 1 then
      if fits_instrmntLegExecGrpComp : instrmntLegExecGrpComp_.length < 256 ^ 2 then
        pure ({ pad2, rbcHeaderMeComp, orderId, clOrdId, origClOrdId, securityId, execId, trdRegTsEntryTime, trdRegTsTimePriority, price, stopPx, marketSegmentId, leavesQty, cumQty, cxlQty, orderQty, expireDate, matchInstCrossId, partyIdExecutingUnit, partyIdSessionId, partyIdExecutingTrader, partyIdEnteringTrader, execRestatementReason, partyIdEnteringFirm, productComplex, ordStatus, execType, side, ordType, tradingCapacity, timeInForce, execInst, tradingSessionSubId, applSeqIndicator, account, partyIdPositionAccount, positionEffect, partyIdTakeUpTradingFirm, partyIdOrderOriginationFirm, partyIdBeneficiary, partyIdLocationId, custOrderHandlingInst, complianceText, freeText1, freeText2, freeText3, triggered, crossed, pad6, legOrdGrpComp := ⟨legOrdGrpComp_, fits_legOrdGrpComp⟩, fillsGrpComp := ⟨fillsGrpComp_, fits_fillsGrpComp⟩, instrmntLegExecGrpComp := ⟨instrmntLegExecGrpComp_, fits_instrmntLegExecGrpComp⟩ }, bytes)
      else none
    else none
  else none

theorem encode_length_pos (message : OrderExecReportBroadcast) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : OrderExecReportBroadcast) : (encode message).length ≤ 2105594 := by
  have bound_legOrdGrpComp := message.legOrdGrpComp.length_lt
  have bound_fillsGrpComp := message.fillsGrpComp.length_lt
  have bound_instrmntLegExecGrpComp := message.instrmntLegExecGrpComp.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, RbcHeaderMeComp.encode_length, encodeUIntLE_length, encodeUInt_length, OrdStatus.encode_length, ExecType.encode_length, PositionEffect.encode_length, encodeMany_length_const LegOrdGrpComp.encode 8 LegOrdGrpComp.encode_length, encodeMany_length_const FillsGrpComp.encode 24 FillsGrpComp.encode_length, encodeMany_length_const InstrmntLegExecGrpComp.encode 32 InstrmntLegExecGrpComp.encode_length]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeMany_bounded 1 LegOrdGrpComp.encode LegOrdGrpComp.decode LegOrdGrpComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeMany_bounded 1 FillsGrpComp.encode FillsGrpComp.decode FillsGrpComp.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 InstrmntLegExecGrpComp.encode InstrmntLegExecGrpComp.decode InstrmntLegExecGrpComp.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.legOrdGrpComp.length_lt, dite_eq_left message.fillsGrpComp.length_lt, dite_eq_left message.instrmntLegExecGrpComp.length_lt]
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
  marketSegmentId : BitVec 32
  leavesQty : BitVec 32
  cumQty : BitVec 32
  cxlQty : BitVec 32
  execRestatementReason : BitVec 16
  side : BitVec 8
  productComplex : BitVec 8
  ordStatus : OrdStatus
  execType : ExecType
  triggered : BitVec 8
  crossed : BitVec 8
  pad5 : Alpha 5
  fillsGrpComp : Bounded 1 FillsGrpComp
  instrmntLegExecGrpComp : Bounded 2 InstrmntLegExecGrpComp
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
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.leavesQty
    ++ (encodeUIntLE 4 message.cumQty
    ++ (encodeUIntLE 4 message.cxlQty
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.instrmntLegExecGrpComp.val.length)
    ++ (encodeUIntLE 2 message.execRestatementReason
    ++ (encodeUInt 1 message.side
    ++ (encodeUInt 1 message.productComplex
    ++ (OrdStatus.encode message.ordStatus
    ++ (ExecType.encode message.execType
    ++ (encodeUInt 1 message.triggered
    ++ (encodeUInt 1 message.crossed
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.fillsGrpComp.val.length)
    ++ (Alpha.encode message.pad5
    ++ (encodeMany FillsGrpComp.encode message.fillsGrpComp.val
    ++ (encodeMany InstrmntLegExecGrpComp.encode message.instrmntLegExecGrpComp.val))))))))))))))))))))))))

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
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (leavesQty, bytes) ← decodeUIntLE 4 bytes
  let (cumQty, bytes) ← decodeUIntLE 4 bytes
  let (cxlQty, bytes) ← decodeUIntLE 4 bytes
  let (noLegExecs, bytes) ← decodeUIntLE 2 bytes
  let (execRestatementReason, bytes) ← decodeUIntLE 2 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (productComplex, bytes) ← decodeUInt 1 bytes
  let (ordStatus, bytes) ← OrdStatus.decode bytes
  let (execType, bytes) ← ExecType.decode bytes
  let (triggered, bytes) ← decodeUInt 1 bytes
  let (crossed, bytes) ← decodeUInt 1 bytes
  let (noFills, bytes) ← decodeUInt 1 bytes
  let (pad5, bytes) ← Alpha.decode 5 bytes
  let (fillsGrpComp_, bytes) ← decodeMany FillsGrpComp.decode noFills.toNat bytes
  let (instrmntLegExecGrpComp_, bytes) ← decodeMany InstrmntLegExecGrpComp.decode noLegExecs.toNat bytes
  if fits_fillsGrpComp : fillsGrpComp_.length < 256 ^ 1 then
    if fits_instrmntLegExecGrpComp : instrmntLegExecGrpComp_.length < 256 ^ 2 then
      pure ({ pad2, responseHeaderMeComp, orderId, clOrdId, origClOrdId, securityId, execId, trdRegTsEntryTime, trdRegTsTimePriority, marketSegmentId, leavesQty, cumQty, cxlQty, execRestatementReason, side, productComplex, ordStatus, execType, triggered, crossed, pad5, fillsGrpComp := ⟨fillsGrpComp_, fits_fillsGrpComp⟩, instrmntLegExecGrpComp := ⟨instrmntLegExecGrpComp_, fits_instrmntLegExecGrpComp⟩ }, bytes)
    else none
  else none

theorem encode_length_pos (message : OrderExecResponse) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : OrderExecResponse) : (encode message).length ≤ 2103402 := by
  have bound_fillsGrpComp := message.fillsGrpComp.length_lt
  have bound_instrmntLegExecGrpComp := message.instrmntLegExecGrpComp.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, ResponseHeaderMeComp.encode_length, encodeUIntLE_length, encodeUInt_length, OrdStatus.encode_length, ExecType.encode_length, encodeMany_length_const FillsGrpComp.encode 24 FillsGrpComp.encode_length, encodeMany_length_const InstrmntLegExecGrpComp.encode 32 InstrmntLegExecGrpComp.encode_length]
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeMany_bounded 1 FillsGrpComp.encode FillsGrpComp.decode FillsGrpComp.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 InstrmntLegExecGrpComp.encode InstrmntLegExecGrpComp.decode InstrmntLegExecGrpComp.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.fillsGrpComp.length_lt, dite_eq_left message.instrmntLegExecGrpComp.length_lt]
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
  productComplex : BitVec 8
  massActionType : BitVec 8
  massActionReason : BitVec 8
  pad2v2 : Alpha 2
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
    ++ (encodeUInt 1 message.productComplex
    ++ (encodeUInt 1 message.massActionType
    ++ (encodeUInt 1 message.massActionReason
    ++ (Alpha.encode message.pad2v2
    ++ (encodeMany NotAffectedSecuritiesGrpComp.encode message.notAffectedSecuritiesGrpComp.val)))))))))))

def decode (bytes : List UInt8) : Option (QuoteActivationNotification × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderMeComp, bytes) ← RbcHeaderMeComp.decode bytes
  let (massActionReportId, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (partyIdEnteringTrader, bytes) ← decodeUIntLE 4 bytes
  let (noNotAffectedSecurities, bytes) ← decodeUIntLE 2 bytes
  let (partyIdEnteringFirm, bytes) ← decodeUInt 1 bytes
  let (productComplex, bytes) ← decodeUInt 1 bytes
  let (massActionType, bytes) ← decodeUInt 1 bytes
  let (massActionReason, bytes) ← decodeUInt 1 bytes
  let (pad2v2, bytes) ← Alpha.decode 2 bytes
  let (notAffectedSecuritiesGrpComp_, bytes) ← decodeMany NotAffectedSecuritiesGrpComp.decode noNotAffectedSecurities.toNat bytes
  if fits_notAffectedSecuritiesGrpComp : notAffectedSecuritiesGrpComp_.length < 256 ^ 2 then
    pure ({ pad2, rbcHeaderMeComp, massActionReportId, marketSegmentId, partyIdEnteringTrader, partyIdEnteringFirm, productComplex, massActionType, massActionReason, pad2v2, notAffectedSecuritiesGrpComp := ⟨notAffectedSecuritiesGrpComp_, fits_notAffectedSecuritiesGrpComp⟩ }, bytes)
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
theorem encode_length_le (message : QuoteActivationResponse) : (encode message).length ≤ 524354 := by
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

/-- Quote Event Grp Comp: 40 bytes -/
structure QuoteEventGrpComp where
  securityId : BitVec 64
  quoteEventPx : BitVec 64
  quoteMsgId : BitVec 64
  quoteEventMatchId : BitVec 32
  quoteEventExecId : BitVec 32
  quoteEventQty : BitVec 32
  quoteEventType : BitVec 8
  quoteEventSide : BitVec 8
  quoteEventLiquidityInd : BitVec 8
  quoteEventReason : BitVec 8
  deriving DecidableEq, Repr

namespace QuoteEventGrpComp

def encode (message : QuoteEventGrpComp) : List UInt8 :=
  encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.quoteEventPx
    ++ (encodeUIntLE 8 message.quoteMsgId
    ++ (encodeUIntLE 4 message.quoteEventMatchId
    ++ (encodeUIntLE 4 message.quoteEventExecId
    ++ (encodeUIntLE 4 message.quoteEventQty
    ++ (encodeUInt 1 message.quoteEventType
    ++ (encodeUInt 1 message.quoteEventSide
    ++ (encodeUInt 1 message.quoteEventLiquidityInd
    ++ (encodeUInt 1 message.quoteEventReason)))))))))

def decode (bytes : List UInt8) : Option (QuoteEventGrpComp × List UInt8) := do
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (quoteEventPx, bytes) ← decodeUIntLE 8 bytes
  let (quoteMsgId, bytes) ← decodeUIntLE 8 bytes
  let (quoteEventMatchId, bytes) ← decodeUIntLE 4 bytes
  let (quoteEventExecId, bytes) ← decodeUIntLE 4 bytes
  let (quoteEventQty, bytes) ← decodeUIntLE 4 bytes
  let (quoteEventType, bytes) ← decodeUInt 1 bytes
  let (quoteEventSide, bytes) ← decodeUInt 1 bytes
  let (quoteEventLiquidityInd, bytes) ← decodeUInt 1 bytes
  let (quoteEventReason, bytes) ← decodeUInt 1 bytes
  pure ({ securityId, quoteEventPx, quoteMsgId, quoteEventMatchId, quoteEventExecId, quoteEventQty, quoteEventType, quoteEventSide, quoteEventLiquidityInd, quoteEventReason }, bytes)

@[simp] theorem encode_length (message : QuoteEventGrpComp) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length]

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
  rw [decodeUInt_encodeUInt, some_bind]
  rfl

end QuoteEventGrpComp

/-- Quote Leg Exec Grp Comp: 32 bytes -/
structure QuoteLegExecGrpComp where
  legSecurityId : BitVec 64
  legLastPx : BitVec 64
  legLastQty : BitVec 32
  legExecId : BitVec 32
  legSide : BitVec 8
  noQuoteEventsIndex : BitVec 8
  pad6 : Alpha 6
  deriving DecidableEq, Repr

namespace QuoteLegExecGrpComp

def encode (message : QuoteLegExecGrpComp) : List UInt8 :=
  encodeUIntLE 8 message.legSecurityId
    ++ (encodeUIntLE 8 message.legLastPx
    ++ (encodeUIntLE 4 message.legLastQty
    ++ (encodeUIntLE 4 message.legExecId
    ++ (encodeUInt 1 message.legSide
    ++ (encodeUInt 1 message.noQuoteEventsIndex
    ++ (Alpha.encode message.pad6))))))

def decode (bytes : List UInt8) : Option (QuoteLegExecGrpComp × List UInt8) := do
  let (legSecurityId, bytes) ← decodeUIntLE 8 bytes
  let (legLastPx, bytes) ← decodeUIntLE 8 bytes
  let (legLastQty, bytes) ← decodeUIntLE 4 bytes
  let (legExecId, bytes) ← decodeUIntLE 4 bytes
  let (legSide, bytes) ← decodeUInt 1 bytes
  let (noQuoteEventsIndex, bytes) ← decodeUInt 1 bytes
  let (pad6, bytes) ← Alpha.decode 6 bytes
  pure ({ legSecurityId, legLastPx, legLastQty, legExecId, legSide, noQuoteEventsIndex, pad6 }, bytes)

@[simp] theorem encode_length (message : QuoteLegExecGrpComp) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, encodeUInt_length, Alpha.encode_length]

theorem encode_length_pos (message : QuoteLegExecGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : QuoteLegExecGrpComp) (rest : List UInt8) :
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
    ++ (RbcHeaderMeComp.encode message.rbcHeaderMeComp
    ++ (encodeUIntLE 8 message.execId
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 2 (BitVec.ofNat (8 * 2) message.quoteLegExecGrpComp.val.length)
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.quoteEventGrpComp.val.length)
    ++ (Alpha.encode message.pad1
    ++ (encodeMany QuoteEventGrpComp.encode message.quoteEventGrpComp.val
    ++ (encodeMany QuoteLegExecGrpComp.encode message.quoteLegExecGrpComp.val))))))))

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
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : QuoteExecutionReport) : (encode message).length ≤ 2107394 := by
  have bound_quoteEventGrpComp := message.quoteEventGrpComp.length_lt
  have bound_quoteLegExecGrpComp := message.quoteLegExecGrpComp.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, RbcHeaderMeComp.encode_length, encodeUIntLE_length, encodeUInt_length, encodeMany_length_const QuoteEventGrpComp.encode 40 QuoteEventGrpComp.encode_length, encodeMany_length_const QuoteLegExecGrpComp.encode 32 QuoteLegExecGrpComp.encode_length]
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeMany_bounded 1 QuoteEventGrpComp.encode QuoteEventGrpComp.decode QuoteEventGrpComp.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 2 QuoteLegExecGrpComp.encode QuoteLegExecGrpComp.decode QuoteLegExecGrpComp.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.quoteEventGrpComp.length_lt, dite_eq_left message.quoteLegExecGrpComp.length_lt]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : QuoteExecutionReport) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end QuoteExecutionReport

/-- Rfq Response: 66 bytes -/
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

@[simp] theorem encode_length (message : RfqResponse) : (encode message).length = 66 := by
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
theorem encode_length_le (message : Reject) : (encode message).length ≤ 65608 := by
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

/-- Risk Notification Broadcast: 82 bytes -/
structure RiskNotificationBroadcast where
  pad2 : Alpha 2
  rbcHeaderComp : RbcHeaderComp
  transactTime : BitVec 64
  tradeDate : BitVec 32
  partyDetailIdExecutingUnit : BitVec 32
  requestingPartyIdExecutingSystem : BitVec 32
  marketId : BitVec 16
  listUpdateAction : ListUpdateAction
  riskLimitAction : BitVec 8
  requestingPartyEnteringFirm : Alpha 9
  requestingPartyClearingFirm : Alpha 9
  pad6 : Alpha 6
  deriving DecidableEq, Repr

namespace RiskNotificationBroadcast

def encode (message : RiskNotificationBroadcast) : List UInt8 :=
  Alpha.encode message.pad2
    ++ (RbcHeaderComp.encode message.rbcHeaderComp
    ++ (encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 4 message.tradeDate
    ++ (encodeUIntLE 4 message.partyDetailIdExecutingUnit
    ++ (encodeUIntLE 4 message.requestingPartyIdExecutingSystem
    ++ (encodeUIntLE 2 message.marketId
    ++ (ListUpdateAction.encode message.listUpdateAction
    ++ (encodeUInt 1 message.riskLimitAction
    ++ (Alpha.encode message.requestingPartyEnteringFirm
    ++ (Alpha.encode message.requestingPartyClearingFirm
    ++ (Alpha.encode message.pad6)))))))))))

def decode (bytes : List UInt8) : Option (RiskNotificationBroadcast × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderComp, bytes) ← RbcHeaderComp.decode bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (tradeDate, bytes) ← decodeUIntLE 4 bytes
  let (partyDetailIdExecutingUnit, bytes) ← decodeUIntLE 4 bytes
  let (requestingPartyIdExecutingSystem, bytes) ← decodeUIntLE 4 bytes
  let (marketId, bytes) ← decodeUIntLE 2 bytes
  let (listUpdateAction, bytes) ← ListUpdateAction.decode bytes
  let (riskLimitAction, bytes) ← decodeUInt 1 bytes
  let (requestingPartyEnteringFirm, bytes) ← Alpha.decode 9 bytes
  let (requestingPartyClearingFirm, bytes) ← Alpha.decode 9 bytes
  let (pad6, bytes) ← Alpha.decode 6 bytes
  pure ({ pad2, rbcHeaderComp, transactTime, tradeDate, partyDetailIdExecutingUnit, requestingPartyIdExecutingSystem, marketId, listUpdateAction, riskLimitAction, requestingPartyEnteringFirm, requestingPartyClearingFirm, pad6 }, bytes)

@[simp] theorem encode_length (message : RiskNotificationBroadcast) : (encode message).length = 82 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RbcHeaderComp.encode_length, encodeUIntLE_length, ListUpdateAction.encode_length, encodeUInt_length]

theorem encode_length_pos (message : RiskNotificationBroadcast) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RiskNotificationBroadcast) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : RiskNotificationBroadcast) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end RiskNotificationBroadcast

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

/-- Tes Approve Broadcast -/
structure TesApproveBroadcast where
  pad2 : Alpha 2
  rbcHeaderComp : RbcHeaderComp
  securityId : BitVec 64
  lastPx : BitVec 64
  transactTime : BitVec 64
  underlyingPx : BitVec 64
  underlyingQty : BitVec 64
  transBkdTime : BitVec 64
  relatedClosePrice : BitVec 64
  marketSegmentId : BitVec 32
  packageId : BitVec 32
  tesExecId : BitVec 32
  allocQty : BitVec 32
  allocId : BitVec 32
  underlyingSettlementDate : BitVec 32
  underlyingMaturityDate : BitVec 32
  relatedTradeId : BitVec 32
  relatedMarketSegmentId : BitVec 32
  relatedTradeQuantity : BitVec 32
  trdType : BitVec 16
  side : BitVec 8
  tradePublishIndicator : BitVec 8
  productComplex : BitVec 8
  tradeReportType : BitVec 8
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
  custOrderHandlingInst : Alpha 1
  complianceText : Alpha 20
  underlyingSecurityId : Alpha 12
  underlyingSecurityDesc : Alpha 30
  underlyingCurrency : Alpha 3
  underlyingIssuer : Alpha 30
  pad3 : Alpha 3
  instrumentEventGrpComp : Bounded 1 InstrumentEventGrpComp
  instrumentAttributeGrpComp : Bounded 1 InstrumentAttributeGrpComp
  underlyingStipGrpComp : Bounded 1 UnderlyingStipGrpComp
  deriving DecidableEq, Repr

namespace TesApproveBroadcast

def encode (message : TesApproveBroadcast) : List UInt8 :=
  Alpha.encode message.pad2
    ++ (RbcHeaderComp.encode message.rbcHeaderComp
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.lastPx
    ++ (encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 8 message.underlyingPx
    ++ (encodeUIntLE 8 message.underlyingQty
    ++ (encodeUIntLE 8 message.transBkdTime
    ++ (encodeUIntLE 8 message.relatedClosePrice
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.packageId
    ++ (encodeUIntLE 4 message.tesExecId
    ++ (encodeUIntLE 4 message.allocQty
    ++ (encodeUIntLE 4 message.allocId
    ++ (encodeUIntLE 4 message.underlyingSettlementDate
    ++ (encodeUIntLE 4 message.underlyingMaturityDate
    ++ (encodeUIntLE 4 message.relatedTradeId
    ++ (encodeUIntLE 4 message.relatedMarketSegmentId
    ++ (encodeUIntLE 4 message.relatedTradeQuantity
    ++ (encodeUIntLE 2 message.trdType
    ++ (encodeUInt 1 message.side
    ++ (encodeUInt 1 message.tradePublishIndicator
    ++ (encodeUInt 1 message.productComplex
    ++ (encodeUInt 1 message.tradeReportType
    ++ (encodeUInt 1 message.tradingCapacity
    ++ (encodeUInt 1 message.partyIdSettlementLocation
    ++ (encodeUInt 1 message.tradeAllocStatus
    ++ (encodeUInt 1 message.hedgeType
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.instrumentEventGrpComp.val.length)
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.instrumentAttributeGrpComp.val.length)
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.underlyingStipGrpComp.val.length)
    ++ (MessageEventSource.encode message.messageEventSource
    ++ (Alpha.encode message.tradeReportId
    ++ (Alpha.encode message.partyExecutingFirm
    ++ (Alpha.encode message.partyExecutingTrader
    ++ (encodeUInt 1 message.partyIdEnteringFirm
    ++ (Alpha.encode message.partyEnteringTrader
    ++ (PositionEffect.encode message.positionEffect
    ++ (Alpha.encode message.rootPartyExecutingFirm
    ++ (Alpha.encode message.rootPartyExecutingTrader
    ++ (Alpha.encode message.freeText1
    ++ (Alpha.encode message.freeText2
    ++ (Alpha.encode message.freeText3
    ++ (Alpha.encode message.partyIdTakeUpTradingFirm
    ++ (Alpha.encode message.account
    ++ (Alpha.encode message.partyIdPositionAccount
    ++ (Alpha.encode message.partyIdOrderOriginationFirm
    ++ (Alpha.encode message.partyIdBeneficiary
    ++ (Alpha.encode message.partyIdLocationId
    ++ (Alpha.encode message.custOrderHandlingInst
    ++ (Alpha.encode message.complianceText
    ++ (Alpha.encode message.underlyingSecurityId
    ++ (Alpha.encode message.underlyingSecurityDesc
    ++ (Alpha.encode message.underlyingCurrency
    ++ (Alpha.encode message.underlyingIssuer
    ++ (Alpha.encode message.pad3
    ++ (encodeMany InstrumentEventGrpComp.encode message.instrumentEventGrpComp.val
    ++ (encodeMany InstrumentAttributeGrpComp.encode message.instrumentAttributeGrpComp.val
    ++ (encodeMany UnderlyingStipGrpComp.encode message.underlyingStipGrpComp.val))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (TesApproveBroadcast × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderComp, bytes) ← RbcHeaderComp.decode bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (underlyingPx, bytes) ← decodeUIntLE 8 bytes
  let (underlyingQty, bytes) ← decodeUIntLE 8 bytes
  let (transBkdTime, bytes) ← decodeUIntLE 8 bytes
  let (relatedClosePrice, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (packageId, bytes) ← decodeUIntLE 4 bytes
  let (tesExecId, bytes) ← decodeUIntLE 4 bytes
  let (allocQty, bytes) ← decodeUIntLE 4 bytes
  let (allocId, bytes) ← decodeUIntLE 4 bytes
  let (underlyingSettlementDate, bytes) ← decodeUIntLE 4 bytes
  let (underlyingMaturityDate, bytes) ← decodeUIntLE 4 bytes
  let (relatedTradeId, bytes) ← decodeUIntLE 4 bytes
  let (relatedMarketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (relatedTradeQuantity, bytes) ← decodeUIntLE 4 bytes
  let (trdType, bytes) ← decodeUIntLE 2 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (tradePublishIndicator, bytes) ← decodeUInt 1 bytes
  let (productComplex, bytes) ← decodeUInt 1 bytes
  let (tradeReportType, bytes) ← decodeUInt 1 bytes
  let (tradingCapacity, bytes) ← decodeUInt 1 bytes
  let (partyIdSettlementLocation, bytes) ← decodeUInt 1 bytes
  let (tradeAllocStatus, bytes) ← decodeUInt 1 bytes
  let (hedgeType, bytes) ← decodeUInt 1 bytes
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
  let (custOrderHandlingInst, bytes) ← Alpha.decode 1 bytes
  let (complianceText, bytes) ← Alpha.decode 20 bytes
  let (underlyingSecurityId, bytes) ← Alpha.decode 12 bytes
  let (underlyingSecurityDesc, bytes) ← Alpha.decode 30 bytes
  let (underlyingCurrency, bytes) ← Alpha.decode 3 bytes
  let (underlyingIssuer, bytes) ← Alpha.decode 30 bytes
  let (pad3, bytes) ← Alpha.decode 3 bytes
  let (instrumentEventGrpComp_, bytes) ← decodeMany InstrumentEventGrpComp.decode noEvents.toNat bytes
  let (instrumentAttributeGrpComp_, bytes) ← decodeMany InstrumentAttributeGrpComp.decode noInstrAttrib.toNat bytes
  let (underlyingStipGrpComp_, bytes) ← decodeMany UnderlyingStipGrpComp.decode noUnderlyingStips.toNat bytes
  if fits_instrumentEventGrpComp : instrumentEventGrpComp_.length < 256 ^ 1 then
    if fits_instrumentAttributeGrpComp : instrumentAttributeGrpComp_.length < 256 ^ 1 then
      if fits_underlyingStipGrpComp : underlyingStipGrpComp_.length < 256 ^ 1 then
        pure ({ pad2, rbcHeaderComp, securityId, lastPx, transactTime, underlyingPx, underlyingQty, transBkdTime, relatedClosePrice, marketSegmentId, packageId, tesExecId, allocQty, allocId, underlyingSettlementDate, underlyingMaturityDate, relatedTradeId, relatedMarketSegmentId, relatedTradeQuantity, trdType, side, tradePublishIndicator, productComplex, tradeReportType, tradingCapacity, partyIdSettlementLocation, tradeAllocStatus, hedgeType, messageEventSource, tradeReportId, partyExecutingFirm, partyExecutingTrader, partyIdEnteringFirm, partyEnteringTrader, positionEffect, rootPartyExecutingFirm, rootPartyExecutingTrader, freeText1, freeText2, freeText3, partyIdTakeUpTradingFirm, account, partyIdPositionAccount, partyIdOrderOriginationFirm, partyIdBeneficiary, partyIdLocationId, custOrderHandlingInst, complianceText, underlyingSecurityId, underlyingSecurityDesc, underlyingCurrency, underlyingIssuer, pad3, instrumentEventGrpComp := ⟨instrumentEventGrpComp_, fits_instrumentEventGrpComp⟩, instrumentAttributeGrpComp := ⟨instrumentAttributeGrpComp_, fits_instrumentAttributeGrpComp⟩, underlyingStipGrpComp := ⟨underlyingStipGrpComp_, fits_underlyingStipGrpComp⟩ }, bytes)
      else none
    else none
  else none

theorem encode_length_pos (message : TesApproveBroadcast) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : TesApproveBroadcast) : (encode message).length ≤ 22826 := by
  have bound_instrumentEventGrpComp := message.instrumentEventGrpComp.length_lt
  have bound_instrumentAttributeGrpComp := message.instrumentAttributeGrpComp.length_lt
  have bound_underlyingStipGrpComp := message.underlyingStipGrpComp.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, RbcHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length, MessageEventSource.encode_length, PositionEffect.encode_length, encodeMany_length_const InstrumentEventGrpComp.encode 8 InstrumentEventGrpComp.encode_length, encodeMany_length_const InstrumentAttributeGrpComp.encode 40 InstrumentAttributeGrpComp.encode_length, encodeMany_length_const UnderlyingStipGrpComp.encode 40 UnderlyingStipGrpComp.encode_length]
  omega

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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
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
  rw [List.append_assoc, decodeMany_bounded 1 InstrumentEventGrpComp.encode InstrumentEventGrpComp.decode InstrumentEventGrpComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeMany_bounded 1 InstrumentAttributeGrpComp.encode InstrumentAttributeGrpComp.decode InstrumentAttributeGrpComp.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 UnderlyingStipGrpComp.encode UnderlyingStipGrpComp.decode UnderlyingStipGrpComp.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.instrumentEventGrpComp.length_lt, dite_eq_left message.instrumentAttributeGrpComp.length_lt, dite_eq_left message.underlyingStipGrpComp.length_lt]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : TesApproveBroadcast) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

end TesApproveBroadcast

/-- Side Alloc Grp Bc Comp: 24 bytes -/
structure SideAllocGrpBcComp where
  individualAllocId : BitVec 32
  allocQty : BitVec 32
  partyExecutingFirm : Alpha 5
  partyExecutingTrader : Alpha 6
  side : BitVec 8
  tradeAllocStatus : BitVec 8
  pad3 : Alpha 3
  deriving DecidableEq, Repr

namespace SideAllocGrpBcComp

def encode (message : SideAllocGrpBcComp) : List UInt8 :=
  encodeUIntLE 4 message.individualAllocId
    ++ (encodeUIntLE 4 message.allocQty
    ++ (Alpha.encode message.partyExecutingFirm
    ++ (Alpha.encode message.partyExecutingTrader
    ++ (encodeUInt 1 message.side
    ++ (encodeUInt 1 message.tradeAllocStatus
    ++ (Alpha.encode message.pad3))))))

def decode (bytes : List UInt8) : Option (SideAllocGrpBcComp × List UInt8) := do
  let (individualAllocId, bytes) ← decodeUIntLE 4 bytes
  let (allocQty, bytes) ← decodeUIntLE 4 bytes
  let (partyExecutingFirm, bytes) ← Alpha.decode 5 bytes
  let (partyExecutingTrader, bytes) ← Alpha.decode 6 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (tradeAllocStatus, bytes) ← decodeUInt 1 bytes
  let (pad3, bytes) ← Alpha.decode 3 bytes
  pure ({ individualAllocId, allocQty, partyExecutingFirm, partyExecutingTrader, side, tradeAllocStatus, pad3 }, bytes)

@[simp] theorem encode_length (message : SideAllocGrpBcComp) : (encode message).length = 24 := by
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
  underlyingPx : BitVec 64
  underlyingQty : BitVec 64
  transBkdTime : BitVec 64
  relatedClosePrice : BitVec 64
  marketSegmentId : BitVec 32
  packageId : BitVec 32
  tesExecId : BitVec 32
  underlyingSettlementDate : BitVec 32
  underlyingMaturityDate : BitVec 32
  relatedTradeId : BitVec 32
  relatedMarketSegmentId : BitVec 32
  relatedTradeQuantity : BitVec 32
  trdType : BitVec 16
  tradeReportType : BitVec 8
  productComplex : BitVec 8
  tradePublishIndicator : BitVec 8
  partyIdSettlementLocation : BitVec 8
  hedgeType : BitVec 8
  messageEventSource : MessageEventSource
  tradeReportText : Alpha 20
  tradeReportId : Alpha 20
  rootPartyExecutingFirm : Alpha 5
  rootPartyExecutingTrader : Alpha 6
  underlyingSecurityId : Alpha 12
  underlyingSecurityDesc : Alpha 30
  underlyingCurrency : Alpha 3
  underlyingIssuer : Alpha 30
  pad6 : Alpha 6
  sideAllocGrpBcComp : Bounded 1 SideAllocGrpBcComp
  instrumentEventGrpComp : Bounded 1 InstrumentEventGrpComp
  instrumentAttributeGrpComp : Bounded 1 InstrumentAttributeGrpComp
  underlyingStipGrpComp : Bounded 1 UnderlyingStipGrpComp
  deriving DecidableEq, Repr

namespace TesBroadcast

def encode (message : TesBroadcast) : List UInt8 :=
  Alpha.encode message.pad2
    ++ (RbcHeaderComp.encode message.rbcHeaderComp
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.lastPx
    ++ (encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 8 message.underlyingPx
    ++ (encodeUIntLE 8 message.underlyingQty
    ++ (encodeUIntLE 8 message.transBkdTime
    ++ (encodeUIntLE 8 message.relatedClosePrice
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.packageId
    ++ (encodeUIntLE 4 message.tesExecId
    ++ (encodeUIntLE 4 message.underlyingSettlementDate
    ++ (encodeUIntLE 4 message.underlyingMaturityDate
    ++ (encodeUIntLE 4 message.relatedTradeId
    ++ (encodeUIntLE 4 message.relatedMarketSegmentId
    ++ (encodeUIntLE 4 message.relatedTradeQuantity
    ++ (encodeUIntLE 2 message.trdType
    ++ (encodeUInt 1 message.tradeReportType
    ++ (encodeUInt 1 message.productComplex
    ++ (encodeUInt 1 message.tradePublishIndicator
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.instrumentEventGrpComp.val.length)
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.instrumentAttributeGrpComp.val.length)
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.underlyingStipGrpComp.val.length)
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.sideAllocGrpBcComp.val.length)
    ++ (encodeUInt 1 message.partyIdSettlementLocation
    ++ (encodeUInt 1 message.hedgeType
    ++ (MessageEventSource.encode message.messageEventSource
    ++ (Alpha.encode message.tradeReportText
    ++ (Alpha.encode message.tradeReportId
    ++ (Alpha.encode message.rootPartyExecutingFirm
    ++ (Alpha.encode message.rootPartyExecutingTrader
    ++ (Alpha.encode message.underlyingSecurityId
    ++ (Alpha.encode message.underlyingSecurityDesc
    ++ (Alpha.encode message.underlyingCurrency
    ++ (Alpha.encode message.underlyingIssuer
    ++ (Alpha.encode message.pad6
    ++ (encodeMany SideAllocGrpBcComp.encode message.sideAllocGrpBcComp.val
    ++ (encodeMany InstrumentEventGrpComp.encode message.instrumentEventGrpComp.val
    ++ (encodeMany InstrumentAttributeGrpComp.encode message.instrumentAttributeGrpComp.val
    ++ (encodeMany UnderlyingStipGrpComp.encode message.underlyingStipGrpComp.val))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (TesBroadcast × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderComp, bytes) ← RbcHeaderComp.decode bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (underlyingPx, bytes) ← decodeUIntLE 8 bytes
  let (underlyingQty, bytes) ← decodeUIntLE 8 bytes
  let (transBkdTime, bytes) ← decodeUIntLE 8 bytes
  let (relatedClosePrice, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (packageId, bytes) ← decodeUIntLE 4 bytes
  let (tesExecId, bytes) ← decodeUIntLE 4 bytes
  let (underlyingSettlementDate, bytes) ← decodeUIntLE 4 bytes
  let (underlyingMaturityDate, bytes) ← decodeUIntLE 4 bytes
  let (relatedTradeId, bytes) ← decodeUIntLE 4 bytes
  let (relatedMarketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (relatedTradeQuantity, bytes) ← decodeUIntLE 4 bytes
  let (trdType, bytes) ← decodeUIntLE 2 bytes
  let (tradeReportType, bytes) ← decodeUInt 1 bytes
  let (productComplex, bytes) ← decodeUInt 1 bytes
  let (tradePublishIndicator, bytes) ← decodeUInt 1 bytes
  let (noEvents, bytes) ← decodeUInt 1 bytes
  let (noInstrAttrib, bytes) ← decodeUInt 1 bytes
  let (noUnderlyingStips, bytes) ← decodeUInt 1 bytes
  let (noSideAllocs, bytes) ← decodeUInt 1 bytes
  let (partyIdSettlementLocation, bytes) ← decodeUInt 1 bytes
  let (hedgeType, bytes) ← decodeUInt 1 bytes
  let (messageEventSource, bytes) ← MessageEventSource.decode bytes
  let (tradeReportText, bytes) ← Alpha.decode 20 bytes
  let (tradeReportId, bytes) ← Alpha.decode 20 bytes
  let (rootPartyExecutingFirm, bytes) ← Alpha.decode 5 bytes
  let (rootPartyExecutingTrader, bytes) ← Alpha.decode 6 bytes
  let (underlyingSecurityId, bytes) ← Alpha.decode 12 bytes
  let (underlyingSecurityDesc, bytes) ← Alpha.decode 30 bytes
  let (underlyingCurrency, bytes) ← Alpha.decode 3 bytes
  let (underlyingIssuer, bytes) ← Alpha.decode 30 bytes
  let (pad6, bytes) ← Alpha.decode 6 bytes
  let (sideAllocGrpBcComp_, bytes) ← decodeMany SideAllocGrpBcComp.decode noSideAllocs.toNat bytes
  let (instrumentEventGrpComp_, bytes) ← decodeMany InstrumentEventGrpComp.decode noEvents.toNat bytes
  let (instrumentAttributeGrpComp_, bytes) ← decodeMany InstrumentAttributeGrpComp.decode noInstrAttrib.toNat bytes
  let (underlyingStipGrpComp_, bytes) ← decodeMany UnderlyingStipGrpComp.decode noUnderlyingStips.toNat bytes
  if fits_sideAllocGrpBcComp : sideAllocGrpBcComp_.length < 256 ^ 1 then
    if fits_instrumentEventGrpComp : instrumentEventGrpComp_.length < 256 ^ 1 then
      if fits_instrumentAttributeGrpComp : instrumentAttributeGrpComp_.length < 256 ^ 1 then
        if fits_underlyingStipGrpComp : underlyingStipGrpComp_.length < 256 ^ 1 then
          pure ({ pad2, rbcHeaderComp, securityId, lastPx, transactTime, underlyingPx, underlyingQty, transBkdTime, relatedClosePrice, marketSegmentId, packageId, tesExecId, underlyingSettlementDate, underlyingMaturityDate, relatedTradeId, relatedMarketSegmentId, relatedTradeQuantity, trdType, tradeReportType, productComplex, tradePublishIndicator, partyIdSettlementLocation, hedgeType, messageEventSource, tradeReportText, tradeReportId, rootPartyExecutingFirm, rootPartyExecutingTrader, underlyingSecurityId, underlyingSecurityDesc, underlyingCurrency, underlyingIssuer, pad6, sideAllocGrpBcComp := ⟨sideAllocGrpBcComp_, fits_sideAllocGrpBcComp⟩, instrumentEventGrpComp := ⟨instrumentEventGrpComp_, fits_instrumentEventGrpComp⟩, instrumentAttributeGrpComp := ⟨instrumentAttributeGrpComp_, fits_instrumentAttributeGrpComp⟩, underlyingStipGrpComp := ⟨underlyingStipGrpComp_, fits_underlyingStipGrpComp⟩ }, bytes)
        else none
      else none
    else none
  else none

theorem encode_length_pos (message : TesBroadcast) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : TesBroadcast) : (encode message).length ≤ 28826 := by
  have bound_sideAllocGrpBcComp := message.sideAllocGrpBcComp.length_lt
  have bound_instrumentEventGrpComp := message.instrumentEventGrpComp.length_lt
  have bound_instrumentAttributeGrpComp := message.instrumentAttributeGrpComp.length_lt
  have bound_underlyingStipGrpComp := message.underlyingStipGrpComp.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, RbcHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length, MessageEventSource.encode_length, encodeMany_length_const SideAllocGrpBcComp.encode 24 SideAllocGrpBcComp.encode_length, encodeMany_length_const InstrumentEventGrpComp.encode 8 InstrumentEventGrpComp.encode_length, encodeMany_length_const InstrumentAttributeGrpComp.encode 40 InstrumentAttributeGrpComp.encode_length, encodeMany_length_const UnderlyingStipGrpComp.encode 40 UnderlyingStipGrpComp.encode_length]
  omega

set_option maxRecDepth 4096 in
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
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUIntLE_encodeUIntLE, some_bind]
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
  rw [List.append_assoc, decodeMany_bounded 1 SideAllocGrpBcComp.encode SideAllocGrpBcComp.decode SideAllocGrpBcComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeMany_bounded 1 InstrumentEventGrpComp.encode InstrumentEventGrpComp.decode InstrumentEventGrpComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeMany_bounded 1 InstrumentAttributeGrpComp.encode InstrumentAttributeGrpComp.decode InstrumentAttributeGrpComp.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 UnderlyingStipGrpComp.encode UnderlyingStipGrpComp.decode UnderlyingStipGrpComp.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.sideAllocGrpBcComp.length_lt, dite_eq_left message.instrumentEventGrpComp.length_lt, dite_eq_left message.instrumentAttributeGrpComp.length_lt, dite_eq_left message.underlyingStipGrpComp.length_lt]
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
  messageEventSource : MessageEventSource
  pad4 : Alpha 4
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
    ++ (MessageEventSource.encode message.messageEventSource
    ++ (Alpha.encode message.pad4))))))))))

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
  let (messageEventSource, bytes) ← MessageEventSource.decode bytes
  let (pad4, bytes) ← Alpha.decode 4 bytes
  pure ({ pad2, rbcHeaderComp, transactTime, marketSegmentId, packageId, tesExecId, allocId, trdType, tradeReportType, messageEventSource, pad4 }, bytes)

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

/-- Tes Trade Broadcast: 258 bytes -/
structure TesTradeBroadcast where
  pad2 : Alpha 2
  rbcHeaderComp : RbcHeaderComp
  securityId : BitVec 64
  lastPx : BitVec 64
  clearingTradePrice : BitVec 64
  transactTime : BitVec 64
  relatedSecurityId : BitVec 64
  packageId : BitVec 32
  lastQty : BitVec 32
  marketSegmentId : BitVec 32
  tradeId : BitVec 32
  tradeDate : BitVec 32
  sideTradeId : BitVec 32
  rootPartyIdSessionId : BitVec 32
  origTradeId : BitVec 32
  clearingTradeQty : BitVec 32
  rootPartyIdExecutingUnit : BitVec 32
  rootPartyIdExecutingTrader : BitVec 32
  rootPartyIdClearingUnit : BitVec 32
  strategyLinkId : BitVec 32
  relatedSymbol : BitVec 32
  totNumTradeReports : BitVec 32
  trdType : BitVec 16
  productComplex : BitVec 8
  relatedProductComplex : BitVec 8
  side : BitVec 8
  tradingCapacity : BitVec 8
  tradeReportType : BitVec 8
  transferReason : BitVec 8
  multiLegReportingType : BitVec 8
  positionEffect : PositionEffect
  account : Alpha 2
  rootPartyIdPositionAccount : Alpha 32
  custOrderHandlingInst : Alpha 1
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
  pad2v2 : Alpha 2
  deriving DecidableEq, Repr

namespace TesTradeBroadcast

def encode (message : TesTradeBroadcast) : List UInt8 :=
  Alpha.encode message.pad2
    ++ (RbcHeaderComp.encode message.rbcHeaderComp
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.lastPx
    ++ (encodeUIntLE 8 message.clearingTradePrice
    ++ (encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 8 message.relatedSecurityId
    ++ (encodeUIntLE 4 message.packageId
    ++ (encodeUIntLE 4 message.lastQty
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.tradeId
    ++ (encodeUIntLE 4 message.tradeDate
    ++ (encodeUIntLE 4 message.sideTradeId
    ++ (encodeUIntLE 4 message.rootPartyIdSessionId
    ++ (encodeUIntLE 4 message.origTradeId
    ++ (encodeUIntLE 4 message.clearingTradeQty
    ++ (encodeUIntLE 4 message.rootPartyIdExecutingUnit
    ++ (encodeUIntLE 4 message.rootPartyIdExecutingTrader
    ++ (encodeUIntLE 4 message.rootPartyIdClearingUnit
    ++ (encodeUIntLE 4 message.strategyLinkId
    ++ (encodeUIntLE 4 message.relatedSymbol
    ++ (encodeUIntLE 4 message.totNumTradeReports
    ++ (encodeUIntLE 2 message.trdType
    ++ (encodeUInt 1 message.productComplex
    ++ (encodeUInt 1 message.relatedProductComplex
    ++ (encodeUInt 1 message.side
    ++ (encodeUInt 1 message.tradingCapacity
    ++ (encodeUInt 1 message.tradeReportType
    ++ (encodeUInt 1 message.transferReason
    ++ (encodeUInt 1 message.multiLegReportingType
    ++ (PositionEffect.encode message.positionEffect
    ++ (Alpha.encode message.account
    ++ (Alpha.encode message.rootPartyIdPositionAccount
    ++ (Alpha.encode message.custOrderHandlingInst
    ++ (Alpha.encode message.freeText1
    ++ (Alpha.encode message.freeText2
    ++ (Alpha.encode message.freeText3
    ++ (Alpha.encode message.rootPartyExecutingFirm
    ++ (Alpha.encode message.rootPartyExecutingTrader
    ++ (Alpha.encode message.rootPartyClearingFirm
    ++ (Alpha.encode message.rootPartyClearingOrganization
    ++ (Alpha.encode message.rootPartyIdBeneficiary
    ++ (Alpha.encode message.rootPartyIdTakeUpTradingFirm
    ++ (Alpha.encode message.rootPartyIdOrderOriginationFirm
    ++ (Alpha.encode message.pad2v2))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (TesTradeBroadcast × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderComp, bytes) ← RbcHeaderComp.decode bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  let (clearingTradePrice, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (relatedSecurityId, bytes) ← decodeUIntLE 8 bytes
  let (packageId, bytes) ← decodeUIntLE 4 bytes
  let (lastQty, bytes) ← decodeUIntLE 4 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (tradeId, bytes) ← decodeUIntLE 4 bytes
  let (tradeDate, bytes) ← decodeUIntLE 4 bytes
  let (sideTradeId, bytes) ← decodeUIntLE 4 bytes
  let (rootPartyIdSessionId, bytes) ← decodeUIntLE 4 bytes
  let (origTradeId, bytes) ← decodeUIntLE 4 bytes
  let (clearingTradeQty, bytes) ← decodeUIntLE 4 bytes
  let (rootPartyIdExecutingUnit, bytes) ← decodeUIntLE 4 bytes
  let (rootPartyIdExecutingTrader, bytes) ← decodeUIntLE 4 bytes
  let (rootPartyIdClearingUnit, bytes) ← decodeUIntLE 4 bytes
  let (strategyLinkId, bytes) ← decodeUIntLE 4 bytes
  let (relatedSymbol, bytes) ← decodeUIntLE 4 bytes
  let (totNumTradeReports, bytes) ← decodeUIntLE 4 bytes
  let (trdType, bytes) ← decodeUIntLE 2 bytes
  let (productComplex, bytes) ← decodeUInt 1 bytes
  let (relatedProductComplex, bytes) ← decodeUInt 1 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (tradingCapacity, bytes) ← decodeUInt 1 bytes
  let (tradeReportType, bytes) ← decodeUInt 1 bytes
  let (transferReason, bytes) ← decodeUInt 1 bytes
  let (multiLegReportingType, bytes) ← decodeUInt 1 bytes
  let (positionEffect, bytes) ← PositionEffect.decode bytes
  let (account, bytes) ← Alpha.decode 2 bytes
  let (rootPartyIdPositionAccount, bytes) ← Alpha.decode 32 bytes
  let (custOrderHandlingInst, bytes) ← Alpha.decode 1 bytes
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
  let (pad2v2, bytes) ← Alpha.decode 2 bytes
  pure ({ pad2, rbcHeaderComp, securityId, lastPx, clearingTradePrice, transactTime, relatedSecurityId, packageId, lastQty, marketSegmentId, tradeId, tradeDate, sideTradeId, rootPartyIdSessionId, origTradeId, clearingTradeQty, rootPartyIdExecutingUnit, rootPartyIdExecutingTrader, rootPartyIdClearingUnit, strategyLinkId, relatedSymbol, totNumTradeReports, trdType, productComplex, relatedProductComplex, side, tradingCapacity, tradeReportType, transferReason, multiLegReportingType, positionEffect, account, rootPartyIdPositionAccount, custOrderHandlingInst, freeText1, freeText2, freeText3, rootPartyExecutingFirm, rootPartyExecutingTrader, rootPartyClearingFirm, rootPartyClearingOrganization, rootPartyIdBeneficiary, rootPartyIdTakeUpTradingFirm, rootPartyIdOrderOriginationFirm, pad2v2 }, bytes)

@[simp] theorem encode_length (message : TesTradeBroadcast) : (encode message).length = 258 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RbcHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length, PositionEffect.encode_length]

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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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

/-- Side Alloc Ext Grp Comp: 152 bytes -/
structure SideAllocExtGrpComp where
  complianceId : BitVec 64
  individualAllocId : BitVec 32
  allocQty : BitVec 32
  partyExecutingFirm : Alpha 5
  partyExecutingTrader : Alpha 6
  side : BitVec 8
  tradeAllocStatus : BitVec 8
  tradingCapacity : BitVec 8
  positionEffect : PositionEffect
  account : Alpha 2
  partyIdPositionAccount : Alpha 32
  partyIdTakeUpTradingFirm : Alpha 5
  freeText1 : Alpha 12
  freeText2 : Alpha 12
  freeText3 : Alpha 12
  partyIdOrderOriginationFirm : Alpha 7
  partyIdBeneficiary : Alpha 9
  partyIdLocationId : Alpha 2
  custOrderHandlingInst : Alpha 1
  complianceText : Alpha 20
  pad7 : Alpha 7
  deriving DecidableEq, Repr

namespace SideAllocExtGrpComp

def encode (message : SideAllocExtGrpComp) : List UInt8 :=
  encodeUIntLE 8 message.complianceId
    ++ (encodeUIntLE 4 message.individualAllocId
    ++ (encodeUIntLE 4 message.allocQty
    ++ (Alpha.encode message.partyExecutingFirm
    ++ (Alpha.encode message.partyExecutingTrader
    ++ (encodeUInt 1 message.side
    ++ (encodeUInt 1 message.tradeAllocStatus
    ++ (encodeUInt 1 message.tradingCapacity
    ++ (PositionEffect.encode message.positionEffect
    ++ (Alpha.encode message.account
    ++ (Alpha.encode message.partyIdPositionAccount
    ++ (Alpha.encode message.partyIdTakeUpTradingFirm
    ++ (Alpha.encode message.freeText1
    ++ (Alpha.encode message.freeText2
    ++ (Alpha.encode message.freeText3
    ++ (Alpha.encode message.partyIdOrderOriginationFirm
    ++ (Alpha.encode message.partyIdBeneficiary
    ++ (Alpha.encode message.partyIdLocationId
    ++ (Alpha.encode message.custOrderHandlingInst
    ++ (Alpha.encode message.complianceText
    ++ (Alpha.encode message.pad7))))))))))))))))))))

def decode (bytes : List UInt8) : Option (SideAllocExtGrpComp × List UInt8) := do
  let (complianceId, bytes) ← decodeUIntLE 8 bytes
  let (individualAllocId, bytes) ← decodeUIntLE 4 bytes
  let (allocQty, bytes) ← decodeUIntLE 4 bytes
  let (partyExecutingFirm, bytes) ← Alpha.decode 5 bytes
  let (partyExecutingTrader, bytes) ← Alpha.decode 6 bytes
  let (side, bytes) ← decodeUInt 1 bytes
  let (tradeAllocStatus, bytes) ← decodeUInt 1 bytes
  let (tradingCapacity, bytes) ← decodeUInt 1 bytes
  let (positionEffect, bytes) ← PositionEffect.decode bytes
  let (account, bytes) ← Alpha.decode 2 bytes
  let (partyIdPositionAccount, bytes) ← Alpha.decode 32 bytes
  let (partyIdTakeUpTradingFirm, bytes) ← Alpha.decode 5 bytes
  let (freeText1, bytes) ← Alpha.decode 12 bytes
  let (freeText2, bytes) ← Alpha.decode 12 bytes
  let (freeText3, bytes) ← Alpha.decode 12 bytes
  let (partyIdOrderOriginationFirm, bytes) ← Alpha.decode 7 bytes
  let (partyIdBeneficiary, bytes) ← Alpha.decode 9 bytes
  let (partyIdLocationId, bytes) ← Alpha.decode 2 bytes
  let (custOrderHandlingInst, bytes) ← Alpha.decode 1 bytes
  let (complianceText, bytes) ← Alpha.decode 20 bytes
  let (pad7, bytes) ← Alpha.decode 7 bytes
  pure ({ complianceId, individualAllocId, allocQty, partyExecutingFirm, partyExecutingTrader, side, tradeAllocStatus, tradingCapacity, positionEffect, account, partyIdPositionAccount, partyIdTakeUpTradingFirm, freeText1, freeText2, freeText3, partyIdOrderOriginationFirm, partyIdBeneficiary, partyIdLocationId, custOrderHandlingInst, complianceText, pad7 }, bytes)

@[simp] theorem encode_length (message : SideAllocExtGrpComp) : (encode message).length = 152 := by
  unfold encode
  simp only [List.length_append, encodeUIntLE_length, Alpha.encode_length, encodeUInt_length, PositionEffect.encode_length]

theorem encode_length_pos (message : SideAllocExtGrpComp) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : SideAllocExtGrpComp) (rest : List UInt8) :
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
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [Alpha.decode_encode, some_bind]
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
  underlyingQty : BitVec 64
  relatedClosePrice : BitVec 64
  marketSegmentId : BitVec 32
  packageId : BitVec 32
  tesExecId : BitVec 32
  underlyingSettlementDate : BitVec 32
  underlyingMaturityDate : BitVec 32
  relatedTradeId : BitVec 32
  relatedMarketSegmentId : BitVec 32
  relatedTradeQuantity : BitVec 32
  trdType : BitVec 16
  productComplex : BitVec 8
  tradeReportType : BitVec 8
  tradePublishIndicator : BitVec 8
  hedgeType : BitVec 8
  partyIdSettlementLocation : BitVec 8
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
  instrumentEventGrpComp : Bounded 1 InstrumentEventGrpComp
  instrumentAttributeGrpComp : Bounded 1 InstrumentAttributeGrpComp
  underlyingStipGrpComp : Bounded 1 UnderlyingStipGrpComp
  deriving DecidableEq, Repr

namespace TesUploadBroadcast

def encode (message : TesUploadBroadcast) : List UInt8 :=
  Alpha.encode message.pad2
    ++ (RbcHeaderComp.encode message.rbcHeaderComp
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.lastPx
    ++ (encodeUIntLE 8 message.transBkdTime
    ++ (encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 8 message.underlyingPx
    ++ (encodeUIntLE 8 message.underlyingQty
    ++ (encodeUIntLE 8 message.relatedClosePrice
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.packageId
    ++ (encodeUIntLE 4 message.tesExecId
    ++ (encodeUIntLE 4 message.underlyingSettlementDate
    ++ (encodeUIntLE 4 message.underlyingMaturityDate
    ++ (encodeUIntLE 4 message.relatedTradeId
    ++ (encodeUIntLE 4 message.relatedMarketSegmentId
    ++ (encodeUIntLE 4 message.relatedTradeQuantity
    ++ (encodeUIntLE 2 message.trdType
    ++ (encodeUInt 1 message.productComplex
    ++ (encodeUInt 1 message.tradeReportType
    ++ (encodeUInt 1 message.tradePublishIndicator
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.sideAllocExtGrpComp.val.length)
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.instrumentEventGrpComp.val.length)
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.instrumentAttributeGrpComp.val.length)
    ++ (encodeUInt 1 (BitVec.ofNat (8 * 1) message.underlyingStipGrpComp.val.length)
    ++ (encodeUInt 1 message.hedgeType
    ++ (encodeUInt 1 message.partyIdSettlementLocation
    ++ (MessageEventSource.encode message.messageEventSource
    ++ (Alpha.encode message.tradeReportId
    ++ (Alpha.encode message.rootPartyExecutingFirm
    ++ (Alpha.encode message.rootPartyExecutingTrader
    ++ (Alpha.encode message.underlyingSecurityId
    ++ (Alpha.encode message.underlyingSecurityDesc
    ++ (Alpha.encode message.underlyingCurrency
    ++ (Alpha.encode message.underlyingIssuer
    ++ (Alpha.encode message.pad2v2
    ++ (encodeMany SideAllocExtGrpComp.encode message.sideAllocExtGrpComp.val
    ++ (encodeMany InstrumentEventGrpComp.encode message.instrumentEventGrpComp.val
    ++ (encodeMany InstrumentAttributeGrpComp.encode message.instrumentAttributeGrpComp.val
    ++ (encodeMany UnderlyingStipGrpComp.encode message.underlyingStipGrpComp.val)))))))))))))))))))))))))))))))))))))))

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
  let (underlyingQty, bytes) ← decodeUIntLE 8 bytes
  let (relatedClosePrice, bytes) ← decodeUIntLE 8 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (packageId, bytes) ← decodeUIntLE 4 bytes
  let (tesExecId, bytes) ← decodeUIntLE 4 bytes
  let (underlyingSettlementDate, bytes) ← decodeUIntLE 4 bytes
  let (underlyingMaturityDate, bytes) ← decodeUIntLE 4 bytes
  let (relatedTradeId, bytes) ← decodeUIntLE 4 bytes
  let (relatedMarketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (relatedTradeQuantity, bytes) ← decodeUIntLE 4 bytes
  let (trdType, bytes) ← decodeUIntLE 2 bytes
  let (productComplex, bytes) ← decodeUInt 1 bytes
  let (tradeReportType, bytes) ← decodeUInt 1 bytes
  let (tradePublishIndicator, bytes) ← decodeUInt 1 bytes
  let (noSideAllocs, bytes) ← decodeUInt 1 bytes
  let (noEvents, bytes) ← decodeUInt 1 bytes
  let (noInstrAttrib, bytes) ← decodeUInt 1 bytes
  let (noUnderlyingStips, bytes) ← decodeUInt 1 bytes
  let (hedgeType, bytes) ← decodeUInt 1 bytes
  let (partyIdSettlementLocation, bytes) ← decodeUInt 1 bytes
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
  let (instrumentEventGrpComp_, bytes) ← decodeMany InstrumentEventGrpComp.decode noEvents.toNat bytes
  let (instrumentAttributeGrpComp_, bytes) ← decodeMany InstrumentAttributeGrpComp.decode noInstrAttrib.toNat bytes
  let (underlyingStipGrpComp_, bytes) ← decodeMany UnderlyingStipGrpComp.decode noUnderlyingStips.toNat bytes
  if fits_sideAllocExtGrpComp : sideAllocExtGrpComp_.length < 256 ^ 1 then
    if fits_instrumentEventGrpComp : instrumentEventGrpComp_.length < 256 ^ 1 then
      if fits_instrumentAttributeGrpComp : instrumentAttributeGrpComp_.length < 256 ^ 1 then
        if fits_underlyingStipGrpComp : underlyingStipGrpComp_.length < 256 ^ 1 then
          pure ({ pad2, rbcHeaderComp, securityId, lastPx, transBkdTime, transactTime, underlyingPx, underlyingQty, relatedClosePrice, marketSegmentId, packageId, tesExecId, underlyingSettlementDate, underlyingMaturityDate, relatedTradeId, relatedMarketSegmentId, relatedTradeQuantity, trdType, productComplex, tradeReportType, tradePublishIndicator, hedgeType, partyIdSettlementLocation, messageEventSource, tradeReportId, rootPartyExecutingFirm, rootPartyExecutingTrader, underlyingSecurityId, underlyingSecurityDesc, underlyingCurrency, underlyingIssuer, pad2v2, sideAllocExtGrpComp := ⟨sideAllocExtGrpComp_, fits_sideAllocExtGrpComp⟩, instrumentEventGrpComp := ⟨instrumentEventGrpComp_, fits_instrumentEventGrpComp⟩, instrumentAttributeGrpComp := ⟨instrumentAttributeGrpComp_, fits_instrumentAttributeGrpComp⟩, underlyingStipGrpComp := ⟨underlyingStipGrpComp_, fits_underlyingStipGrpComp⟩ }, bytes)
        else none
      else none
    else none
  else none

theorem encode_length_pos (message : TesUploadBroadcast) : (encode message).length > 0 := by
  unfold encode
  simp only [Alpha.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : TesUploadBroadcast) : (encode message).length ≤ 61442 := by
  have bound_sideAllocExtGrpComp := message.sideAllocExtGrpComp.length_lt
  have bound_instrumentEventGrpComp := message.instrumentEventGrpComp.length_lt
  have bound_instrumentAttributeGrpComp := message.instrumentAttributeGrpComp.length_lt
  have bound_underlyingStipGrpComp := message.underlyingStipGrpComp.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, Alpha.encode_length, RbcHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length, MessageEventSource.encode_length, encodeMany_length_const SideAllocExtGrpComp.encode 152 SideAllocExtGrpComp.encode_length, encodeMany_length_const InstrumentEventGrpComp.encode 8 InstrumentEventGrpComp.encode_length, encodeMany_length_const InstrumentAttributeGrpComp.encode 40 InstrumentAttributeGrpComp.encode_length, encodeMany_length_const UnderlyingStipGrpComp.encode 40 UnderlyingStipGrpComp.encode_length]
  omega

set_option maxRecDepth 4096 in
@[simp] theorem decode_encode (message : TesUploadBroadcast) (rest : List UInt8) :
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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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
  rw [List.append_assoc, decodeMany_bounded 1 SideAllocExtGrpComp.encode SideAllocExtGrpComp.decode SideAllocExtGrpComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeMany_bounded 1 InstrumentEventGrpComp.encode InstrumentEventGrpComp.decode InstrumentEventGrpComp.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeMany_bounded 1 InstrumentAttributeGrpComp.encode InstrumentAttributeGrpComp.decode InstrumentAttributeGrpComp.decode_encode, some_bind]
  dsimp only
  rw [decodeMany_bounded 1 UnderlyingStipGrpComp.encode UnderlyingStipGrpComp.decode UnderlyingStipGrpComp.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.sideAllocExtGrpComp.length_lt, dite_eq_left message.instrumentEventGrpComp.length_lt, dite_eq_left message.instrumentAttributeGrpComp.length_lt, dite_eq_left message.underlyingStipGrpComp.length_lt]
  rfl

/-- Decoded as the whole of a frame: nothing follows -/
theorem decode_encode_nil (message : TesUploadBroadcast) : decode (encode message) = some (message, []) :=
  List.append_nil (encode message) ▸ decode_encode message []

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

/-- Trade Broadcast: 306 bytes -/
structure TradeBroadcast where
  pad2 : Alpha 2
  rbcHeaderComp : RbcHeaderComp
  securityId : BitVec 64
  relatedSecurityId : BitVec 64
  price : BitVec 64
  lastPx : BitVec 64
  sideLastPx : BitVec 64
  clearingTradePrice : BitVec 64
  transactTime : BitVec 64
  orderId : BitVec 64
  clOrdId : BitVec 64
  tradeId : BitVec 32
  origTradeId : BitVec 32
  rootPartyIdExecutingUnit : BitVec 32
  rootPartyIdSessionId : BitVec 32
  rootPartyIdExecutingTrader : BitVec 32
  rootPartyIdClearingUnit : BitVec 32
  cumQty : BitVec 32
  leavesQty : BitVec 32
  marketSegmentId : BitVec 32
  relatedSymbol : BitVec 32
  lastQty : BitVec 32
  sideLastQty : BitVec 32
  clearingTradeQty : BitVec 32
  sideTradeId : BitVec 32
  matchDate : BitVec 32
  trdMatchId : BitVec 32
  strategyLinkId : BitVec 32
  totNumTradeReports : BitVec 32
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
  account : Alpha 2
  rootPartyIdPositionAccount : Alpha 32
  positionEffect : PositionEffect
  custOrderHandlingInst : Alpha 1
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
  pad3 : Alpha 3
  deriving DecidableEq, Repr

namespace TradeBroadcast

def encode (message : TradeBroadcast) : List UInt8 :=
  Alpha.encode message.pad2
    ++ (RbcHeaderComp.encode message.rbcHeaderComp
    ++ (encodeUIntLE 8 message.securityId
    ++ (encodeUIntLE 8 message.relatedSecurityId
    ++ (encodeUIntLE 8 message.price
    ++ (encodeUIntLE 8 message.lastPx
    ++ (encodeUIntLE 8 message.sideLastPx
    ++ (encodeUIntLE 8 message.clearingTradePrice
    ++ (encodeUIntLE 8 message.transactTime
    ++ (encodeUIntLE 8 message.orderId
    ++ (encodeUIntLE 8 message.clOrdId
    ++ (encodeUIntLE 4 message.tradeId
    ++ (encodeUIntLE 4 message.origTradeId
    ++ (encodeUIntLE 4 message.rootPartyIdExecutingUnit
    ++ (encodeUIntLE 4 message.rootPartyIdSessionId
    ++ (encodeUIntLE 4 message.rootPartyIdExecutingTrader
    ++ (encodeUIntLE 4 message.rootPartyIdClearingUnit
    ++ (encodeUIntLE 4 message.cumQty
    ++ (encodeUIntLE 4 message.leavesQty
    ++ (encodeUIntLE 4 message.marketSegmentId
    ++ (encodeUIntLE 4 message.relatedSymbol
    ++ (encodeUIntLE 4 message.lastQty
    ++ (encodeUIntLE 4 message.sideLastQty
    ++ (encodeUIntLE 4 message.clearingTradeQty
    ++ (encodeUIntLE 4 message.sideTradeId
    ++ (encodeUIntLE 4 message.matchDate
    ++ (encodeUIntLE 4 message.trdMatchId
    ++ (encodeUIntLE 4 message.strategyLinkId
    ++ (encodeUIntLE 4 message.totNumTradeReports
    ++ (encodeUInt 1 message.multiLegReportingType
    ++ (encodeUInt 1 message.tradeReportType
    ++ (encodeUInt 1 message.transferReason
    ++ (Alpha.encode message.rootPartyIdBeneficiary
    ++ (Alpha.encode message.rootPartyIdTakeUpTradingFirm
    ++ (Alpha.encode message.rootPartyIdOrderOriginationFirm
    ++ (encodeUInt 1 message.matchType
    ++ (encodeUInt 1 message.matchSubType
    ++ (encodeUInt 1 message.side
    ++ (encodeUInt 1 message.sideLiquidityInd
    ++ (encodeUInt 1 message.tradingCapacity
    ++ (Alpha.encode message.account
    ++ (Alpha.encode message.rootPartyIdPositionAccount
    ++ (PositionEffect.encode message.positionEffect
    ++ (Alpha.encode message.custOrderHandlingInst
    ++ (Alpha.encode message.freeText1
    ++ (Alpha.encode message.freeText2
    ++ (Alpha.encode message.freeText3
    ++ (OrderCategory.encode message.orderCategory
    ++ (encodeUInt 1 message.ordType
    ++ (encodeUInt 1 message.relatedProductComplex
    ++ (encodeUInt 1 message.orderSide
    ++ (Alpha.encode message.rootPartyClearingOrganization
    ++ (Alpha.encode message.rootPartyExecutingFirm
    ++ (Alpha.encode message.rootPartyExecutingTrader
    ++ (Alpha.encode message.rootPartyClearingFirm
    ++ (Alpha.encode message.pad3)))))))))))))))))))))))))))))))))))))))))))))))))))))))

-- a long run of fields nests deeper than the elaborator's default limit
set_option maxRecDepth 4096 in
def decode (bytes : List UInt8) : Option (TradeBroadcast × List UInt8) := do
  let (pad2, bytes) ← Alpha.decode 2 bytes
  let (rbcHeaderComp, bytes) ← RbcHeaderComp.decode bytes
  let (securityId, bytes) ← decodeUIntLE 8 bytes
  let (relatedSecurityId, bytes) ← decodeUIntLE 8 bytes
  let (price, bytes) ← decodeUIntLE 8 bytes
  let (lastPx, bytes) ← decodeUIntLE 8 bytes
  let (sideLastPx, bytes) ← decodeUIntLE 8 bytes
  let (clearingTradePrice, bytes) ← decodeUIntLE 8 bytes
  let (transactTime, bytes) ← decodeUIntLE 8 bytes
  let (orderId, bytes) ← decodeUIntLE 8 bytes
  let (clOrdId, bytes) ← decodeUIntLE 8 bytes
  let (tradeId, bytes) ← decodeUIntLE 4 bytes
  let (origTradeId, bytes) ← decodeUIntLE 4 bytes
  let (rootPartyIdExecutingUnit, bytes) ← decodeUIntLE 4 bytes
  let (rootPartyIdSessionId, bytes) ← decodeUIntLE 4 bytes
  let (rootPartyIdExecutingTrader, bytes) ← decodeUIntLE 4 bytes
  let (rootPartyIdClearingUnit, bytes) ← decodeUIntLE 4 bytes
  let (cumQty, bytes) ← decodeUIntLE 4 bytes
  let (leavesQty, bytes) ← decodeUIntLE 4 bytes
  let (marketSegmentId, bytes) ← decodeUIntLE 4 bytes
  let (relatedSymbol, bytes) ← decodeUIntLE 4 bytes
  let (lastQty, bytes) ← decodeUIntLE 4 bytes
  let (sideLastQty, bytes) ← decodeUIntLE 4 bytes
  let (clearingTradeQty, bytes) ← decodeUIntLE 4 bytes
  let (sideTradeId, bytes) ← decodeUIntLE 4 bytes
  let (matchDate, bytes) ← decodeUIntLE 4 bytes
  let (trdMatchId, bytes) ← decodeUIntLE 4 bytes
  let (strategyLinkId, bytes) ← decodeUIntLE 4 bytes
  let (totNumTradeReports, bytes) ← decodeUIntLE 4 bytes
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
  let (account, bytes) ← Alpha.decode 2 bytes
  let (rootPartyIdPositionAccount, bytes) ← Alpha.decode 32 bytes
  let (positionEffect, bytes) ← PositionEffect.decode bytes
  let (custOrderHandlingInst, bytes) ← Alpha.decode 1 bytes
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
  let (pad3, bytes) ← Alpha.decode 3 bytes
  pure ({ pad2, rbcHeaderComp, securityId, relatedSecurityId, price, lastPx, sideLastPx, clearingTradePrice, transactTime, orderId, clOrdId, tradeId, origTradeId, rootPartyIdExecutingUnit, rootPartyIdSessionId, rootPartyIdExecutingTrader, rootPartyIdClearingUnit, cumQty, leavesQty, marketSegmentId, relatedSymbol, lastQty, sideLastQty, clearingTradeQty, sideTradeId, matchDate, trdMatchId, strategyLinkId, totNumTradeReports, multiLegReportingType, tradeReportType, transferReason, rootPartyIdBeneficiary, rootPartyIdTakeUpTradingFirm, rootPartyIdOrderOriginationFirm, matchType, matchSubType, side, sideLiquidityInd, tradingCapacity, account, rootPartyIdPositionAccount, positionEffect, custOrderHandlingInst, freeText1, freeText2, freeText3, orderCategory, ordType, relatedProductComplex, orderSide, rootPartyClearingOrganization, rootPartyExecutingFirm, rootPartyExecutingTrader, rootPartyClearingFirm, pad3 }, bytes)

@[simp] theorem encode_length (message : TradeBroadcast) : (encode message).length = 306 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, RbcHeaderComp.encode_length, encodeUIntLE_length, encodeUInt_length, PositionEffect.encode_length, OrderCategory.encode_length]

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
  rw [List.append_assoc, decodeUInt_encodeUInt, some_bind]
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

/-- Any Server Payload, selected by Template Id -/
inductive ServerPayload where
  | addComplexInstrumentResponse (message : AddComplexInstrumentResponse) -- 10302
  | addFlexibleInstrumentResponse (message : AddFlexibleInstrumentResponse) -- 10310
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
  | forcedLogoutNotification (message : ForcedLogoutNotification) -- 10012
  | forcedUserLogoutNotification (message : ForcedUserLogoutNotification) -- 10043
  | gatewayResponse (message : GatewayResponse) -- 10021
  | heartbeatNotification (message : HeartbeatNotification) -- 10023
  | inquireEnrichmentRuleIdListResponse (message : InquireEnrichmentRuleIdListResponse) -- 10041
  | inquireMmParameterResponse (message : InquireMmParameterResponse) -- 10306
  | inquireSessionListResponse (message : InquireSessionListResponse) -- 10036
  | inquireUserResponse (message : InquireUserResponse) -- 10039
  | legalNotificationBroadcast (message : LegalNotificationBroadcast) -- 10037
  | logonResponse (message : LogonResponse) -- 10001
  | logoutResponse (message : LogoutResponse) -- 10003
  | mmParameterDefinitionResponse (message : MmParameterDefinitionResponse) -- 10304
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
  | rfqResponse (message : RfqResponse) -- 10402
  | reject (message : Reject) -- 10010
  | retransmitMeMessageResponse (message : RetransmitMeMessageResponse) -- 10027
  | retransmitResponse (message : RetransmitResponse) -- 10009
  | riskNotificationBroadcast (message : RiskNotificationBroadcast) -- 10033
  | serviceAvailabilityBroadcast (message : ServiceAvailabilityBroadcast) -- 10030
  | subscribeResponse (message : SubscribeResponse) -- 10005
  | tesApproveBroadcast (message : TesApproveBroadcast) -- 10607
  | tesBroadcast (message : TesBroadcast) -- 10604
  | tesDeleteBroadcast (message : TesDeleteBroadcast) -- 10606
  | tesExecutionBroadcast (message : TesExecutionBroadcast) -- 10610
  | tesResponse (message : TesResponse) -- 10611
  | tesTradeBroadcast (message : TesTradeBroadcast) -- 10614
  | tesTradingSessionStatusBroadcast (message : TesTradingSessionStatusBroadcast) -- 10615
  | tesUploadBroadcast (message : TesUploadBroadcast) -- 10613
  | tmTradingSessionStatusBroadcast (message : TmTradingSessionStatusBroadcast) -- 10501
  | throttleUpdateNotification (message : ThrottleUpdateNotification) -- 10028
  | tradeBroadcast (message : TradeBroadcast) -- 10500
  | tradingSessionStatusBroadcast (message : TradingSessionStatusBroadcast) -- 10307
  | unsubscribeResponse (message : UnsubscribeResponse) -- 10007
  | userLoginResponse (message : UserLoginResponse) -- 10019
  | userLogoutResponse (message : UserLogoutResponse) -- 10024
  deriving DecidableEq, Repr

namespace ServerPayload

/-- The Template Id each message is sent under -/
def tag : ServerPayload → BitVec 16
  | .addComplexInstrumentResponse _ => 10302
  | .addFlexibleInstrumentResponse _ => 10310
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
  | .forcedLogoutNotification _ => 10012
  | .forcedUserLogoutNotification _ => 10043
  | .gatewayResponse _ => 10021
  | .heartbeatNotification _ => 10023
  | .inquireEnrichmentRuleIdListResponse _ => 10041
  | .inquireMmParameterResponse _ => 10306
  | .inquireSessionListResponse _ => 10036
  | .inquireUserResponse _ => 10039
  | .legalNotificationBroadcast _ => 10037
  | .logonResponse _ => 10001
  | .logoutResponse _ => 10003
  | .mmParameterDefinitionResponse _ => 10304
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
  | .rfqResponse _ => 10402
  | .reject _ => 10010
  | .retransmitMeMessageResponse _ => 10027
  | .retransmitResponse _ => 10009
  | .riskNotificationBroadcast _ => 10033
  | .serviceAvailabilityBroadcast _ => 10030
  | .subscribeResponse _ => 10005
  | .tesApproveBroadcast _ => 10607
  | .tesBroadcast _ => 10604
  | .tesDeleteBroadcast _ => 10606
  | .tesExecutionBroadcast _ => 10610
  | .tesResponse _ => 10611
  | .tesTradeBroadcast _ => 10614
  | .tesTradingSessionStatusBroadcast _ => 10615
  | .tesUploadBroadcast _ => 10613
  | .tmTradingSessionStatusBroadcast _ => 10501
  | .throttleUpdateNotification _ => 10028
  | .tradeBroadcast _ => 10500
  | .tradingSessionStatusBroadcast _ => 10307
  | .unsubscribeResponse _ => 10007
  | .userLoginResponse _ => 10019
  | .userLogoutResponse _ => 10024

def encode : ServerPayload → List UInt8
  | .addComplexInstrumentResponse message => AddComplexInstrumentResponse.encode message
  | .addFlexibleInstrumentResponse message => AddFlexibleInstrumentResponse.encode message
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
  | .forcedLogoutNotification message => ForcedLogoutNotification.encode message
  | .forcedUserLogoutNotification message => ForcedUserLogoutNotification.encode message
  | .gatewayResponse message => GatewayResponse.encode message
  | .heartbeatNotification message => HeartbeatNotification.encode message
  | .inquireEnrichmentRuleIdListResponse message => InquireEnrichmentRuleIdListResponse.encode message
  | .inquireMmParameterResponse message => InquireMmParameterResponse.encode message
  | .inquireSessionListResponse message => InquireSessionListResponse.encode message
  | .inquireUserResponse message => InquireUserResponse.encode message
  | .legalNotificationBroadcast message => LegalNotificationBroadcast.encode message
  | .logonResponse message => LogonResponse.encode message
  | .logoutResponse message => LogoutResponse.encode message
  | .mmParameterDefinitionResponse message => MmParameterDefinitionResponse.encode message
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
  | .rfqResponse message => RfqResponse.encode message
  | .reject message => Reject.encode message
  | .retransmitMeMessageResponse message => RetransmitMeMessageResponse.encode message
  | .retransmitResponse message => RetransmitResponse.encode message
  | .riskNotificationBroadcast message => RiskNotificationBroadcast.encode message
  | .serviceAvailabilityBroadcast message => ServiceAvailabilityBroadcast.encode message
  | .subscribeResponse message => SubscribeResponse.encode message
  | .tesApproveBroadcast message => TesApproveBroadcast.encode message
  | .tesBroadcast message => TesBroadcast.encode message
  | .tesDeleteBroadcast message => TesDeleteBroadcast.encode message
  | .tesExecutionBroadcast message => TesExecutionBroadcast.encode message
  | .tesResponse message => TesResponse.encode message
  | .tesTradeBroadcast message => TesTradeBroadcast.encode message
  | .tesTradingSessionStatusBroadcast message => TesTradingSessionStatusBroadcast.encode message
  | .tesUploadBroadcast message => TesUploadBroadcast.encode message
  | .tmTradingSessionStatusBroadcast message => TmTradingSessionStatusBroadcast.encode message
  | .throttleUpdateNotification message => ThrottleUpdateNotification.encode message
  | .tradeBroadcast message => TradeBroadcast.encode message
  | .tradingSessionStatusBroadcast message => TradingSessionStatusBroadcast.encode message
  | .unsubscribeResponse message => UnsubscribeResponse.encode message
  | .userLoginResponse message => UserLoginResponse.encode message
  | .userLogoutResponse message => UserLogoutResponse.encode message

/-- Decoded from the whole of the frame: a message that reads to its end takes it all, any other must leave nothing -/
def decode (tag : BitVec 16) (bytes : List UInt8) : Option ServerPayload :=
  if tag = 10302 then (AddComplexInstrumentResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.addComplexInstrumentResponse message) else none
  else if tag = 10310 then (AddFlexibleInstrumentResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.addFlexibleInstrumentResponse message) else none
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
  else if tag = 10012 then (ForcedLogoutNotification.decode bytes).map fun message => .forcedLogoutNotification message
  else if tag = 10043 then (ForcedUserLogoutNotification.decode bytes).map fun message => .forcedUserLogoutNotification message
  else if tag = 10021 then (GatewayResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.gatewayResponse message) else none
  else if tag = 10023 then (HeartbeatNotification.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.heartbeatNotification message) else none
  else if tag = 10041 then (InquireEnrichmentRuleIdListResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.inquireEnrichmentRuleIdListResponse message) else none
  else if tag = 10306 then (InquireMmParameterResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.inquireMmParameterResponse message) else none
  else if tag = 10036 then (InquireSessionListResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.inquireSessionListResponse message) else none
  else if tag = 10039 then (InquireUserResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.inquireUserResponse message) else none
  else if tag = 10037 then (LegalNotificationBroadcast.decode bytes).map fun message => .legalNotificationBroadcast message
  else if tag = 10001 then (LogonResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.logonResponse message) else none
  else if tag = 10003 then (LogoutResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.logoutResponse message) else none
  else if tag = 10304 then (MmParameterDefinitionResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.mmParameterDefinitionResponse message) else none
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
  else if tag = 10402 then (RfqResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.rfqResponse message) else none
  else if tag = 10010 then (Reject.decode bytes).map fun message => .reject message
  else if tag = 10027 then (RetransmitMeMessageResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.retransmitMeMessageResponse message) else none
  else if tag = 10009 then (RetransmitResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.retransmitResponse message) else none
  else if tag = 10033 then (RiskNotificationBroadcast.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.riskNotificationBroadcast message) else none
  else if tag = 10030 then (ServiceAvailabilityBroadcast.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.serviceAvailabilityBroadcast message) else none
  else if tag = 10005 then (SubscribeResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.subscribeResponse message) else none
  else if tag = 10607 then (TesApproveBroadcast.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.tesApproveBroadcast message) else none
  else if tag = 10604 then (TesBroadcast.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.tesBroadcast message) else none
  else if tag = 10606 then (TesDeleteBroadcast.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.tesDeleteBroadcast message) else none
  else if tag = 10610 then (TesExecutionBroadcast.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.tesExecutionBroadcast message) else none
  else if tag = 10611 then (TesResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.tesResponse message) else none
  else if tag = 10614 then (TesTradeBroadcast.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.tesTradeBroadcast message) else none
  else if tag = 10615 then (TesTradingSessionStatusBroadcast.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.tesTradingSessionStatusBroadcast message) else none
  else if tag = 10613 then (TesUploadBroadcast.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.tesUploadBroadcast message) else none
  else if tag = 10501 then (TmTradingSessionStatusBroadcast.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.tmTradingSessionStatusBroadcast message) else none
  else if tag = 10028 then (ThrottleUpdateNotification.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.throttleUpdateNotification message) else none
  else if tag = 10500 then (TradeBroadcast.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.tradeBroadcast message) else none
  else if tag = 10307 then (TradingSessionStatusBroadcast.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.tradingSessionStatusBroadcast message) else none
  else if tag = 10007 then (UnsubscribeResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.unsubscribeResponse message) else none
  else if tag = 10019 then (UserLoginResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.userLoginResponse message) else none
  else if tag = 10024 then (UserLogoutResponse.decode bytes).bind fun (message, rest) => if rest.isEmpty then some (.userLogoutResponse message) else none
  else none

theorem decode_encode (message : ServerPayload) :
    decode (tag message) (encode message) = some message := by
  cases message with
  | addComplexInstrumentResponse message => simp [decode, encode, tag, AddComplexInstrumentResponse.decode_encode_nil]
  | addFlexibleInstrumentResponse message => simp [decode, encode, tag, AddFlexibleInstrumentResponse.decode_encode_nil]
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
  | forcedLogoutNotification message => simp [decode, encode, tag, ForcedLogoutNotification.decode_encode]
  | forcedUserLogoutNotification message => simp [decode, encode, tag, ForcedUserLogoutNotification.decode_encode]
  | gatewayResponse message => simp [decode, encode, tag, GatewayResponse.decode_encode_nil]
  | heartbeatNotification message => simp [decode, encode, tag, HeartbeatNotification.decode_encode_nil]
  | inquireEnrichmentRuleIdListResponse message => simp [decode, encode, tag, InquireEnrichmentRuleIdListResponse.decode_encode_nil]
  | inquireMmParameterResponse message => simp [decode, encode, tag, InquireMmParameterResponse.decode_encode_nil]
  | inquireSessionListResponse message => simp [decode, encode, tag, InquireSessionListResponse.decode_encode_nil]
  | inquireUserResponse message => simp [decode, encode, tag, InquireUserResponse.decode_encode_nil]
  | legalNotificationBroadcast message => simp [decode, encode, tag, LegalNotificationBroadcast.decode_encode]
  | logonResponse message => simp [decode, encode, tag, LogonResponse.decode_encode_nil]
  | logoutResponse message => simp [decode, encode, tag, LogoutResponse.decode_encode_nil]
  | mmParameterDefinitionResponse message => simp [decode, encode, tag, MmParameterDefinitionResponse.decode_encode_nil]
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
  | rfqResponse message => simp [decode, encode, tag, RfqResponse.decode_encode_nil]
  | reject message => simp [decode, encode, tag, Reject.decode_encode]
  | retransmitMeMessageResponse message => simp [decode, encode, tag, RetransmitMeMessageResponse.decode_encode_nil]
  | retransmitResponse message => simp [decode, encode, tag, RetransmitResponse.decode_encode_nil]
  | riskNotificationBroadcast message => simp [decode, encode, tag, RiskNotificationBroadcast.decode_encode_nil]
  | serviceAvailabilityBroadcast message => simp [decode, encode, tag, ServiceAvailabilityBroadcast.decode_encode_nil]
  | subscribeResponse message => simp [decode, encode, tag, SubscribeResponse.decode_encode_nil]
  | tesApproveBroadcast message => simp [decode, encode, tag, TesApproveBroadcast.decode_encode_nil]
  | tesBroadcast message => simp [decode, encode, tag, TesBroadcast.decode_encode_nil]
  | tesDeleteBroadcast message => simp [decode, encode, tag, TesDeleteBroadcast.decode_encode_nil]
  | tesExecutionBroadcast message => simp [decode, encode, tag, TesExecutionBroadcast.decode_encode_nil]
  | tesResponse message => simp [decode, encode, tag, TesResponse.decode_encode_nil]
  | tesTradeBroadcast message => simp [decode, encode, tag, TesTradeBroadcast.decode_encode_nil]
  | tesTradingSessionStatusBroadcast message => simp [decode, encode, tag, TesTradingSessionStatusBroadcast.decode_encode_nil]
  | tesUploadBroadcast message => simp [decode, encode, tag, TesUploadBroadcast.decode_encode_nil]
  | tmTradingSessionStatusBroadcast message => simp [decode, encode, tag, TmTradingSessionStatusBroadcast.decode_encode_nil]
  | throttleUpdateNotification message => simp [decode, encode, tag, ThrottleUpdateNotification.decode_encode_nil]
  | tradeBroadcast message => simp [decode, encode, tag, TradeBroadcast.decode_encode_nil]
  | tradingSessionStatusBroadcast message => simp [decode, encode, tag, TradingSessionStatusBroadcast.decode_encode_nil]
  | unsubscribeResponse message => simp [decode, encode, tag, UnsubscribeResponse.decode_encode_nil]
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
  | addComplexInstrumentResponse inner =>
    have bound_inner := AddComplexInstrumentResponse.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | addFlexibleInstrumentResponse inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, AddFlexibleInstrumentResponse.encode_length]
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
  | forcedLogoutNotification inner =>
    have bound_inner := ForcedLogoutNotification.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | forcedUserLogoutNotification inner =>
    have bound_inner := ForcedUserLogoutNotification.encode_length_le inner
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length]
    omega
  | gatewayResponse inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, GatewayResponse.encode_length]
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
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, LogonResponse.encode_length]
    omega
  | logoutResponse inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, LogoutResponse.encode_length]
    omega
  | mmParameterDefinitionResponse inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, MmParameterDefinitionResponse.encode_length]
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
  | serviceAvailabilityBroadcast inner =>
    simp only [ServerPayload.encode, List.length_append, encodeUIntLE_length, ServiceAvailabilityBroadcast.encode_length]
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

end Omi.EurexT7EtiFbeV50Server
