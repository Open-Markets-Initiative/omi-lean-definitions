import Wire

/-!
# TMX Group Sola Order Entry v1.21

Generated from the binary model, with the proofs the model's rules call for: every record
decodes back to what was encoded; a message dispatch selects the message its type names;
a count is written from the list it counts; a length prefix is written from the bytes it frames;
and a packet read to the end of its data decodes to the messages that were written.

Note: Number Of Legs counts New Strategy Instrument Acknowledgement Leg Definition Repeating Block in ascii digits: it is written from the list as its digits, and a list of more than 99 could not be written.

Note: Number Of Quotes In Error counts Bulk Quote Acknowledgement Occurrence in ascii digits: it is written from the list as its digits, and a list of more than 999 could not be written.

Note: Number Of Commands counts Bulk Command Acknowledgement Occurrence in ascii digits: it is written from the list as its digits, and a list of more than 9999 could not be written.

Note: Number Of Usage Blocks counts Risk Limits Usage Occurrence in ascii digits: it is written from the list as its digits, and a list of more than 9999 could not be written.

Note: Nb Of Instruments counts Excluded Instrument Notice Occurrence in ascii digits: it is written from the list as its digits, and a list of more than 9999 could not be written.

Note: Alignment Padding pads to a 4 byte boundary: it is read as the bytes left to the end of the frame, fewer than 4, and the frame's length is trusted to keep the boundary.

Text fields are kept byte for byte, padding included, so what is decoded encodes back unchanged.
Prices with implied decimals are proven as the integers on the wire.
-/

namespace Omi.TmxMxSolaorderentrySailV121Exchange

/-- Connection Acknowledgement: 12 bytes -/
structure ConnectionAcknowledgement where
  currentSessionId : Alpha 4
  lastUserSequenceIdReceived : Alpha 8
  deriving DecidableEq, Repr

namespace ConnectionAcknowledgement

def encode (message : ConnectionAcknowledgement) : List UInt8 :=
  Alpha.encode message.currentSessionId
    ++ (Alpha.encode message.lastUserSequenceIdReceived)

def decode (bytes : List UInt8) : Option (ConnectionAcknowledgement × List UInt8) := do
  let (currentSessionId, bytes) ← Alpha.decode 4 bytes
  let (lastUserSequenceIdReceived, bytes) ← Alpha.decode 8 bytes
  pure ({ currentSessionId, lastUserSequenceIdReceived }, bytes)

@[simp] theorem encode_length (message : ConnectionAcknowledgement) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : ConnectionAcknowledgement) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ConnectionAcknowledgement) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ConnectionAcknowledgement

/-- Disconnection Instruction Acknowledgement: 12 bytes -/
structure DisconnectionInstructionAcknowledgement where
  currentSessionId : Alpha 4
  lastUserSequenceIdReceived : Alpha 8
  deriving DecidableEq, Repr

namespace DisconnectionInstructionAcknowledgement

def encode (message : DisconnectionInstructionAcknowledgement) : List UInt8 :=
  Alpha.encode message.currentSessionId
    ++ (Alpha.encode message.lastUserSequenceIdReceived)

def decode (bytes : List UInt8) : Option (DisconnectionInstructionAcknowledgement × List UInt8) := do
  let (currentSessionId, bytes) ← Alpha.decode 4 bytes
  let (lastUserSequenceIdReceived, bytes) ← Alpha.decode 8 bytes
  pure ({ currentSessionId, lastUserSequenceIdReceived }, bytes)

@[simp] theorem encode_length (message : DisconnectionInstructionAcknowledgement) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : DisconnectionInstructionAcknowledgement) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DisconnectionInstructionAcknowledgement) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end DisconnectionInstructionAcknowledgement

/-- Heartbeat Question: 20 bytes -/
structure HeartbeatQuestion where
  userSequenceIdFirstUserSequenceIdForNextcurrentHeartbeatPeriod : Alpha 8
  lastExchangeMessageIdSentToParticipant : Alpha 6
  tradingEngineTimestampLocalHhmmss : Alpha 6
  deriving DecidableEq, Repr

namespace HeartbeatQuestion

def encode (message : HeartbeatQuestion) : List UInt8 :=
  Alpha.encode message.userSequenceIdFirstUserSequenceIdForNextcurrentHeartbeatPeriod
    ++ (Alpha.encode message.lastExchangeMessageIdSentToParticipant
    ++ (Alpha.encode message.tradingEngineTimestampLocalHhmmss))

def decode (bytes : List UInt8) : Option (HeartbeatQuestion × List UInt8) := do
  let (userSequenceIdFirstUserSequenceIdForNextcurrentHeartbeatPeriod, bytes) ← Alpha.decode 8 bytes
  let (lastExchangeMessageIdSentToParticipant, bytes) ← Alpha.decode 6 bytes
  let (tradingEngineTimestampLocalHhmmss, bytes) ← Alpha.decode 6 bytes
  pure ({ userSequenceIdFirstUserSequenceIdForNextcurrentHeartbeatPeriod, lastExchangeMessageIdSentToParticipant, tradingEngineTimestampLocalHhmmss }, bytes)

@[simp] theorem encode_length (message : HeartbeatQuestion) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : HeartbeatQuestion) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : HeartbeatQuestion) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end HeartbeatQuestion

/-- Out Of Sequence: 22 bytes -/
structure OutOfSequence where
  receivedUserSequenceId : Alpha 8
  expectedLastUserSequenceId : Alpha 8
  userMessageTimestampLocalHhmmss : Alpha 6
  deriving DecidableEq, Repr

namespace OutOfSequence

def encode (message : OutOfSequence) : List UInt8 :=
  Alpha.encode message.receivedUserSequenceId
    ++ (Alpha.encode message.expectedLastUserSequenceId
    ++ (Alpha.encode message.userMessageTimestampLocalHhmmss))

def decode (bytes : List UInt8) : Option (OutOfSequence × List UInt8) := do
  let (receivedUserSequenceId, bytes) ← Alpha.decode 8 bytes
  let (expectedLastUserSequenceId, bytes) ← Alpha.decode 8 bytes
  let (userMessageTimestampLocalHhmmss, bytes) ← Alpha.decode 6 bytes
  pure ({ receivedUserSequenceId, expectedLastUserSequenceId, userMessageTimestampLocalHhmmss }, bytes)

@[simp] theorem encode_length (message : OutOfSequence) : (encode message).length = 22 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : OutOfSequence) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OutOfSequence) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OutOfSequence

/-- Technical Error Notice: 218 bytes -/
structure TechnicalErrorNotice where
  receivedMessageType : Alpha 2
  precedingUserSequenceIdReceivedZeroesIfNone : Alpha 8
  errorCode : Alpha 4
  errorPosition : Alpha 4
  errorMessage : Alpha 100
  startOfMessageInError : Alpha 100
  deriving DecidableEq, Repr

namespace TechnicalErrorNotice

def encode (message : TechnicalErrorNotice) : List UInt8 :=
  Alpha.encode message.receivedMessageType
    ++ (Alpha.encode message.precedingUserSequenceIdReceivedZeroesIfNone
    ++ (Alpha.encode message.errorCode
    ++ (Alpha.encode message.errorPosition
    ++ (Alpha.encode message.errorMessage
    ++ (Alpha.encode message.startOfMessageInError)))))

def decode (bytes : List UInt8) : Option (TechnicalErrorNotice × List UInt8) := do
  let (receivedMessageType, bytes) ← Alpha.decode 2 bytes
  let (precedingUserSequenceIdReceivedZeroesIfNone, bytes) ← Alpha.decode 8 bytes
  let (errorCode, bytes) ← Alpha.decode 4 bytes
  let (errorPosition, bytes) ← Alpha.decode 4 bytes
  let (errorMessage, bytes) ← Alpha.decode 100 bytes
  let (startOfMessageInError, bytes) ← Alpha.decode 100 bytes
  pure ({ receivedMessageType, precedingUserSequenceIdReceivedZeroesIfNone, errorCode, errorPosition, errorMessage, startOfMessageInError }, bytes)

@[simp] theorem encode_length (message : TechnicalErrorNotice) : (encode message).length = 218 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : TechnicalErrorNotice) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : TechnicalErrorNotice) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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

end TechnicalErrorNotice

/-- Disconnection Acknowledgement: 12 bytes -/
structure DisconnectionAcknowledgement where
  currentSessionId : Alpha 4
  lastUserSequenceIdReceived : Alpha 8
  deriving DecidableEq, Repr

namespace DisconnectionAcknowledgement

def encode (message : DisconnectionAcknowledgement) : List UInt8 :=
  Alpha.encode message.currentSessionId
    ++ (Alpha.encode message.lastUserSequenceIdReceived)

def decode (bytes : List UInt8) : Option (DisconnectionAcknowledgement × List UInt8) := do
  let (currentSessionId, bytes) ← Alpha.decode 4 bytes
  let (lastUserSequenceIdReceived, bytes) ← Alpha.decode 8 bytes
  pure ({ currentSessionId, lastUserSequenceIdReceived }, bytes)

@[simp] theorem encode_length (message : DisconnectionAcknowledgement) : (encode message).length = 12 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : DisconnectionAcknowledgement) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : DisconnectionAcknowledgement) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end DisconnectionAcknowledgement

/-- End Of Transmission: 18 bytes -/
structure EndOfTransmission where
  endedSessionId : Alpha 4
  lastUserSequenceIdReceivedIfNoBusinessMessageHasBeenReceivedOnThisConnectionThisFieldIsEqualToZeroes : Alpha 8
  tradingEngineTimestampLocalHhmmss : Alpha 6
  deriving DecidableEq, Repr

namespace EndOfTransmission

def encode (message : EndOfTransmission) : List UInt8 :=
  Alpha.encode message.endedSessionId
    ++ (Alpha.encode message.lastUserSequenceIdReceivedIfNoBusinessMessageHasBeenReceivedOnThisConnectionThisFieldIsEqualToZeroes
    ++ (Alpha.encode message.tradingEngineTimestampLocalHhmmss))

def decode (bytes : List UInt8) : Option (EndOfTransmission × List UInt8) := do
  let (endedSessionId, bytes) ← Alpha.decode 4 bytes
  let (lastUserSequenceIdReceivedIfNoBusinessMessageHasBeenReceivedOnThisConnectionThisFieldIsEqualToZeroes, bytes) ← Alpha.decode 8 bytes
  let (tradingEngineTimestampLocalHhmmss, bytes) ← Alpha.decode 6 bytes
  pure ({ endedSessionId, lastUserSequenceIdReceivedIfNoBusinessMessageHasBeenReceivedOnThisConnectionThisFieldIsEqualToZeroes, tradingEngineTimestampLocalHhmmss }, bytes)

@[simp] theorem encode_length (message : EndOfTransmission) : (encode message).length = 18 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : EndOfTransmission) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : EndOfTransmission) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end EndOfTransmission

/-- Outgoing Messages Header: 22 bytes -/
structure OutgoingMessagesHeader where
  tradingEngineTimestampLocalHhmmss : Alpha 6
  userSequenceId : Alpha 8
  exchangeMessageId : Alpha 6
  gapSequenceId : Alpha 2
  deriving DecidableEq, Repr

namespace OutgoingMessagesHeader

def encode (message : OutgoingMessagesHeader) : List UInt8 :=
  Alpha.encode message.tradingEngineTimestampLocalHhmmss
    ++ (Alpha.encode message.userSequenceId
    ++ (Alpha.encode message.exchangeMessageId
    ++ (Alpha.encode message.gapSequenceId)))

def decode (bytes : List UInt8) : Option (OutgoingMessagesHeader × List UInt8) := do
  let (tradingEngineTimestampLocalHhmmss, bytes) ← Alpha.decode 6 bytes
  let (userSequenceId, bytes) ← Alpha.decode 8 bytes
  let (exchangeMessageId, bytes) ← Alpha.decode 6 bytes
  let (gapSequenceId, bytes) ← Alpha.decode 2 bytes
  pure ({ tradingEngineTimestampLocalHhmmss, userSequenceId, exchangeMessageId, gapSequenceId }, bytes)

@[simp] theorem encode_length (message : OutgoingMessagesHeader) : (encode message).length = 22 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : OutgoingMessagesHeader) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OutgoingMessagesHeader) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OutgoingMessagesHeader

/-- Clearing Data: 20 bytes -/
structure ClearingData where
  clearingInstruction : Alpha 12
  accountType : Alpha 1
  openClose : Alpha 1
  hedgeSpec : Alpha 1
  filler5 : Alpha 5
  deriving DecidableEq, Repr

namespace ClearingData

def encode (message : ClearingData) : List UInt8 :=
  Alpha.encode message.clearingInstruction
    ++ (Alpha.encode message.accountType
    ++ (Alpha.encode message.openClose
    ++ (Alpha.encode message.hedgeSpec
    ++ (Alpha.encode message.filler5))))

def decode (bytes : List UInt8) : Option (ClearingData × List UInt8) := do
  let (clearingInstruction, bytes) ← Alpha.decode 12 bytes
  let (accountType, bytes) ← Alpha.decode 1 bytes
  let (openClose, bytes) ← Alpha.decode 1 bytes
  let (hedgeSpec, bytes) ← Alpha.decode 1 bytes
  let (filler5, bytes) ← Alpha.decode 5 bytes
  pure ({ clearingInstruction, accountType, openClose, hedgeSpec, filler5 }, bytes)

@[simp] theorem encode_length (message : ClearingData) : (encode message).length = 20 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : ClearingData) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ClearingData) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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

end ClearingData

/-- Owner Data: 50 bytes -/
structure OwnerData where
  memo : Alpha 50
  deriving DecidableEq, Repr

namespace OwnerData

def encode (message : OwnerData) : List UInt8 :=
  Alpha.encode message.memo

def decode (bytes : List UInt8) : Option (OwnerData × List UInt8) := do
  let (memo, bytes) ← Alpha.decode 50 bytes
  pure ({ memo }, bytes)

@[simp] theorem encode_length (message : OwnerData) : (encode message).length = 50 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : OwnerData) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OwnerData) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end OwnerData

/-- Order Reply: 134 bytes -/
structure OrderReply where
  outgoingMessagesHeader : OutgoingMessagesHeader
  group : Alpha 2
  instrument : Alpha 4
  traderId : Alpha 8
  orderId : Alpha 8
  status : Alpha 1
  verbSide : Alpha 1
  quantityRemaining : Alpha 8
  assignedPrice : Alpha 10
  clearingData : ClearingData
  ownerData : OwnerData
  deriving DecidableEq, Repr

namespace OrderReply

def encode (message : OrderReply) : List UInt8 :=
  OutgoingMessagesHeader.encode message.outgoingMessagesHeader
    ++ (Alpha.encode message.group
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.traderId
    ++ (Alpha.encode message.orderId
    ++ (Alpha.encode message.status
    ++ (Alpha.encode message.verbSide
    ++ (Alpha.encode message.quantityRemaining
    ++ (Alpha.encode message.assignedPrice
    ++ (ClearingData.encode message.clearingData
    ++ (OwnerData.encode message.ownerData))))))))))

def decode (bytes : List UInt8) : Option (OrderReply × List UInt8) := do
  let (outgoingMessagesHeader, bytes) ← OutgoingMessagesHeader.decode bytes
  let (group, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (traderId, bytes) ← Alpha.decode 8 bytes
  let (orderId, bytes) ← Alpha.decode 8 bytes
  let (status, bytes) ← Alpha.decode 1 bytes
  let (verbSide, bytes) ← Alpha.decode 1 bytes
  let (quantityRemaining, bytes) ← Alpha.decode 8 bytes
  let (assignedPrice, bytes) ← Alpha.decode 10 bytes
  let (clearingData, bytes) ← ClearingData.decode bytes
  let (ownerData, bytes) ← OwnerData.decode bytes
  pure ({ outgoingMessagesHeader, group, instrument, traderId, orderId, status, verbSide, quantityRemaining, assignedPrice, clearingData, ownerData }, bytes)

@[simp] theorem encode_length (message : OrderReply) : (encode message).length = 134 := by
  unfold encode
  simp only [List.length_append, OutgoingMessagesHeader.encode_length, Alpha.encode_length, ClearingData.encode_length, OwnerData.encode_length]

theorem encode_length_pos (message : OrderReply) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderReply) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, OutgoingMessagesHeader.decode_encode, some_bind]
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
  rw [List.append_assoc, ClearingData.decode_encode, some_bind]
  dsimp only
  rw [OwnerData.decode_encode, some_bind]
  rfl

end OrderReply

/-- Error Notice: 126 bytes -/
structure ErrorNotice where
  outgoingMessagesHeader : OutgoingMessagesHeader
  errorCode : Alpha 4
  errorDescription : Alpha 100
  deriving DecidableEq, Repr

namespace ErrorNotice

def encode (message : ErrorNotice) : List UInt8 :=
  OutgoingMessagesHeader.encode message.outgoingMessagesHeader
    ++ (Alpha.encode message.errorCode
    ++ (Alpha.encode message.errorDescription))

def decode (bytes : List UInt8) : Option (ErrorNotice × List UInt8) := do
  let (outgoingMessagesHeader, bytes) ← OutgoingMessagesHeader.decode bytes
  let (errorCode, bytes) ← Alpha.decode 4 bytes
  let (errorDescription, bytes) ← Alpha.decode 100 bytes
  pure ({ outgoingMessagesHeader, errorCode, errorDescription }, bytes)

@[simp] theorem encode_length (message : ErrorNotice) : (encode message).length = 126 := by
  unfold encode
  simp only [List.length_append, OutgoingMessagesHeader.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : ErrorNotice) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ErrorNotice) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, OutgoingMessagesHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end ErrorNotice

/-- Bulk Quote Data Acknowledgement: 40 bytes -/
structure BulkQuoteDataAcknowledgement where
  outgoingMessagesHeader : OutgoingMessagesHeader
  group : Alpha 2
  traderId : Alpha 8
  quoteIdIdentifiesTradersQuoteOnThisGroup : Alpha 8
  deriving DecidableEq, Repr

namespace BulkQuoteDataAcknowledgement

def encode (message : BulkQuoteDataAcknowledgement) : List UInt8 :=
  OutgoingMessagesHeader.encode message.outgoingMessagesHeader
    ++ (Alpha.encode message.group
    ++ (Alpha.encode message.traderId
    ++ (Alpha.encode message.quoteIdIdentifiesTradersQuoteOnThisGroup)))

def decode (bytes : List UInt8) : Option (BulkQuoteDataAcknowledgement × List UInt8) := do
  let (outgoingMessagesHeader, bytes) ← OutgoingMessagesHeader.decode bytes
  let (group, bytes) ← Alpha.decode 2 bytes
  let (traderId, bytes) ← Alpha.decode 8 bytes
  let (quoteIdIdentifiesTradersQuoteOnThisGroup, bytes) ← Alpha.decode 8 bytes
  pure ({ outgoingMessagesHeader, group, traderId, quoteIdIdentifiesTradersQuoteOnThisGroup }, bytes)

@[simp] theorem encode_length (message : BulkQuoteDataAcknowledgement) : (encode message).length = 40 := by
  unfold encode
  simp only [List.length_append, OutgoingMessagesHeader.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : BulkQuoteDataAcknowledgement) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BulkQuoteDataAcknowledgement) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, OutgoingMessagesHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end BulkQuoteDataAcknowledgement

/-- Order Acknowledgement: 148 bytes -/
structure OrderAcknowledgement where
  outgoingMessagesHeader : OutgoingMessagesHeader
  group : Alpha 2
  instrument : Alpha 4
  traderId : Alpha 8
  orderId : Alpha 8
  status : Alpha 1
  verbSide : Alpha 1
  quantity : Alpha 8
  assignedPrice : Alpha 10
  clearingData : ClearingData
  ownerData : OwnerData
  originalOrderId : Alpha 8
  filler6 : Alpha 6
  deriving DecidableEq, Repr

namespace OrderAcknowledgement

def encode (message : OrderAcknowledgement) : List UInt8 :=
  OutgoingMessagesHeader.encode message.outgoingMessagesHeader
    ++ (Alpha.encode message.group
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.traderId
    ++ (Alpha.encode message.orderId
    ++ (Alpha.encode message.status
    ++ (Alpha.encode message.verbSide
    ++ (Alpha.encode message.quantity
    ++ (Alpha.encode message.assignedPrice
    ++ (ClearingData.encode message.clearingData
    ++ (OwnerData.encode message.ownerData
    ++ (Alpha.encode message.originalOrderId
    ++ (Alpha.encode message.filler6))))))))))))

def decode (bytes : List UInt8) : Option (OrderAcknowledgement × List UInt8) := do
  let (outgoingMessagesHeader, bytes) ← OutgoingMessagesHeader.decode bytes
  let (group, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (traderId, bytes) ← Alpha.decode 8 bytes
  let (orderId, bytes) ← Alpha.decode 8 bytes
  let (status, bytes) ← Alpha.decode 1 bytes
  let (verbSide, bytes) ← Alpha.decode 1 bytes
  let (quantity, bytes) ← Alpha.decode 8 bytes
  let (assignedPrice, bytes) ← Alpha.decode 10 bytes
  let (clearingData, bytes) ← ClearingData.decode bytes
  let (ownerData, bytes) ← OwnerData.decode bytes
  let (originalOrderId, bytes) ← Alpha.decode 8 bytes
  let (filler6, bytes) ← Alpha.decode 6 bytes
  pure ({ outgoingMessagesHeader, group, instrument, traderId, orderId, status, verbSide, quantity, assignedPrice, clearingData, ownerData, originalOrderId, filler6 }, bytes)

@[simp] theorem encode_length (message : OrderAcknowledgement) : (encode message).length = 148 := by
  unfold encode
  simp only [List.length_append, OutgoingMessagesHeader.encode_length, Alpha.encode_length, ClearingData.encode_length, OwnerData.encode_length]

theorem encode_length_pos (message : OrderAcknowledgement) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderAcknowledgement) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, OutgoingMessagesHeader.decode_encode, some_bind]
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
  rw [List.append_assoc, ClearingData.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OwnerData.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderAcknowledgement

/-- Global Cancellation Confirmation: 33 bytes -/
structure GlobalCancellationConfirmation where
  outgoingMessagesHeader : OutgoingMessagesHeader
  group : Alpha 2
  traderId : Alpha 8
  typeOfCancellationOnlyQQuotesOnlyCanBeReturned : Alpha 1
  deriving DecidableEq, Repr

namespace GlobalCancellationConfirmation

def encode (message : GlobalCancellationConfirmation) : List UInt8 :=
  OutgoingMessagesHeader.encode message.outgoingMessagesHeader
    ++ (Alpha.encode message.group
    ++ (Alpha.encode message.traderId
    ++ (Alpha.encode message.typeOfCancellationOnlyQQuotesOnlyCanBeReturned)))

def decode (bytes : List UInt8) : Option (GlobalCancellationConfirmation × List UInt8) := do
  let (outgoingMessagesHeader, bytes) ← OutgoingMessagesHeader.decode bytes
  let (group, bytes) ← Alpha.decode 2 bytes
  let (traderId, bytes) ← Alpha.decode 8 bytes
  let (typeOfCancellationOnlyQQuotesOnlyCanBeReturned, bytes) ← Alpha.decode 1 bytes
  pure ({ outgoingMessagesHeader, group, traderId, typeOfCancellationOnlyQQuotesOnlyCanBeReturned }, bytes)

@[simp] theorem encode_length (message : GlobalCancellationConfirmation) : (encode message).length = 33 := by
  unfold encode
  simp only [List.length_append, OutgoingMessagesHeader.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : GlobalCancellationConfirmation) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : GlobalCancellationConfirmation) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, OutgoingMessagesHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end GlobalCancellationConfirmation

/-- Order Modification Acknowledgement: 126 bytes -/
structure OrderModificationAcknowledgement where
  group : Alpha 2
  instrument : Alpha 4
  traderId : Alpha 8
  orderId : Alpha 8
  status : Alpha 1
  verbSide : Alpha 1
  quantity : Alpha 8
  assignedPrice : Alpha 10
  clearingData : ClearingData
  ownerData : OwnerData
  originalOrderId : Alpha 8
  filler6 : Alpha 6
  deriving DecidableEq, Repr

namespace OrderModificationAcknowledgement

def encode (message : OrderModificationAcknowledgement) : List UInt8 :=
  Alpha.encode message.group
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.traderId
    ++ (Alpha.encode message.orderId
    ++ (Alpha.encode message.status
    ++ (Alpha.encode message.verbSide
    ++ (Alpha.encode message.quantity
    ++ (Alpha.encode message.assignedPrice
    ++ (ClearingData.encode message.clearingData
    ++ (OwnerData.encode message.ownerData
    ++ (Alpha.encode message.originalOrderId
    ++ (Alpha.encode message.filler6)))))))))))

def decode (bytes : List UInt8) : Option (OrderModificationAcknowledgement × List UInt8) := do
  let (group, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (traderId, bytes) ← Alpha.decode 8 bytes
  let (orderId, bytes) ← Alpha.decode 8 bytes
  let (status, bytes) ← Alpha.decode 1 bytes
  let (verbSide, bytes) ← Alpha.decode 1 bytes
  let (quantity, bytes) ← Alpha.decode 8 bytes
  let (assignedPrice, bytes) ← Alpha.decode 10 bytes
  let (clearingData, bytes) ← ClearingData.decode bytes
  let (ownerData, bytes) ← OwnerData.decode bytes
  let (originalOrderId, bytes) ← Alpha.decode 8 bytes
  let (filler6, bytes) ← Alpha.decode 6 bytes
  pure ({ group, instrument, traderId, orderId, status, verbSide, quantity, assignedPrice, clearingData, ownerData, originalOrderId, filler6 }, bytes)

@[simp] theorem encode_length (message : OrderModificationAcknowledgement) : (encode message).length = 126 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, ClearingData.encode_length, OwnerData.encode_length]

theorem encode_length_pos (message : OrderModificationAcknowledgement) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderModificationAcknowledgement) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, ClearingData.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OwnerData.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderModificationAcknowledgement

/-- New Strategy Instrument Acknowledgement Leg Definition Repeating Block: 16 bytes -/
structure NewStrategyInstrumentAcknowledgementLegDefinitionRepeatingBlock where
  legGroup : Alpha 2
  legInstrument : Alpha 4
  legVerb : Alpha 1
  filler1 : Alpha 1
  legQuantityRatio : Alpha 8
  deriving DecidableEq, Repr

namespace NewStrategyInstrumentAcknowledgementLegDefinitionRepeatingBlock

def encode (message : NewStrategyInstrumentAcknowledgementLegDefinitionRepeatingBlock) : List UInt8 :=
  Alpha.encode message.legGroup
    ++ (Alpha.encode message.legInstrument
    ++ (Alpha.encode message.legVerb
    ++ (Alpha.encode message.filler1
    ++ (Alpha.encode message.legQuantityRatio))))

def decode (bytes : List UInt8) : Option (NewStrategyInstrumentAcknowledgementLegDefinitionRepeatingBlock × List UInt8) := do
  let (legGroup, bytes) ← Alpha.decode 2 bytes
  let (legInstrument, bytes) ← Alpha.decode 4 bytes
  let (legVerb, bytes) ← Alpha.decode 1 bytes
  let (filler1, bytes) ← Alpha.decode 1 bytes
  let (legQuantityRatio, bytes) ← Alpha.decode 8 bytes
  pure ({ legGroup, legInstrument, legVerb, filler1, legQuantityRatio }, bytes)

@[simp] theorem encode_length (message : NewStrategyInstrumentAcknowledgementLegDefinitionRepeatingBlock) : (encode message).length = 16 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : NewStrategyInstrumentAcknowledgementLegDefinitionRepeatingBlock) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : NewStrategyInstrumentAcknowledgementLegDefinitionRepeatingBlock) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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

end NewStrategyInstrumentAcknowledgementLegDefinitionRepeatingBlock

/-- New Strategy Instrument Acknowledgement -/
structure NewStrategyInstrumentAcknowledgement where
  outgoingMessagesHeader : OutgoingMessagesHeader
  strategyGroup : Alpha 2
  strategyInstrument : Alpha 4
  creationStatus : Alpha 1
  newStrategyInstrumentAcknowledgementLegDefinitionRepeatingBlock : Digited 2 NewStrategyInstrumentAcknowledgementLegDefinitionRepeatingBlock
  deriving DecidableEq, Repr

namespace NewStrategyInstrumentAcknowledgement

def encode (message : NewStrategyInstrumentAcknowledgement) : List UInt8 :=
  OutgoingMessagesHeader.encode message.outgoingMessagesHeader
    ++ (Alpha.encode message.strategyGroup
    ++ (Alpha.encode message.strategyInstrument
    ++ (Alpha.encode message.creationStatus
    ++ (encodeDigits 2 message.newStrategyInstrumentAcknowledgementLegDefinitionRepeatingBlock.val.length
    ++ (encodeMany NewStrategyInstrumentAcknowledgementLegDefinitionRepeatingBlock.encode message.newStrategyInstrumentAcknowledgementLegDefinitionRepeatingBlock.val)))))

def decode (bytes : List UInt8) : Option (NewStrategyInstrumentAcknowledgement × List UInt8) := do
  let (outgoingMessagesHeader, bytes) ← OutgoingMessagesHeader.decode bytes
  let (strategyGroup, bytes) ← Alpha.decode 2 bytes
  let (strategyInstrument, bytes) ← Alpha.decode 4 bytes
  let (creationStatus, bytes) ← Alpha.decode 1 bytes
  let (numberOfLegs, bytes) ← decodeDigits 2 bytes
  let (newStrategyInstrumentAcknowledgementLegDefinitionRepeatingBlock_, bytes) ← decodeMany NewStrategyInstrumentAcknowledgementLegDefinitionRepeatingBlock.decode numberOfLegs bytes
  if fits_newStrategyInstrumentAcknowledgementLegDefinitionRepeatingBlock : newStrategyInstrumentAcknowledgementLegDefinitionRepeatingBlock_.length < 10 ^ 2 then
    pure ({ outgoingMessagesHeader, strategyGroup, strategyInstrument, creationStatus, newStrategyInstrumentAcknowledgementLegDefinitionRepeatingBlock := ⟨newStrategyInstrumentAcknowledgementLegDefinitionRepeatingBlock_, fits_newStrategyInstrumentAcknowledgementLegDefinitionRepeatingBlock⟩ }, bytes)
  else none

theorem encode_length_pos (message : NewStrategyInstrumentAcknowledgement) : (encode message).length > 0 := by
  unfold encode
  simp only [OutgoingMessagesHeader.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : NewStrategyInstrumentAcknowledgement) : (encode message).length ≤ 1615 := by
  have bound_newStrategyInstrumentAcknowledgementLegDefinitionRepeatingBlock := message.newStrategyInstrumentAcknowledgementLegDefinitionRepeatingBlock.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, OutgoingMessagesHeader.encode_length, Alpha.encode_length, encodeDigits_length, encodeMany_length_const NewStrategyInstrumentAcknowledgementLegDefinitionRepeatingBlock.encode 16 NewStrategyInstrumentAcknowledgementLegDefinitionRepeatingBlock.encode_length]
  omega

@[simp] theorem decode_encode (message : NewStrategyInstrumentAcknowledgement) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, OutgoingMessagesHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.newStrategyInstrumentAcknowledgementLegDefinitionRepeatingBlock.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany NewStrategyInstrumentAcknowledgementLegDefinitionRepeatingBlock.encode NewStrategyInstrumentAcknowledgementLegDefinitionRepeatingBlock.decode NewStrategyInstrumentAcknowledgementLegDefinitionRepeatingBlock.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.newStrategyInstrumentAcknowledgementLegDefinitionRepeatingBlock.length_lt]
  rfl

end NewStrategyInstrumentAcknowledgement

/-- Standard Acknowledgement: 32 bytes -/
structure StandardAcknowledgement where
  outgoingMessagesHeader : OutgoingMessagesHeader
  traderId : Alpha 8
  originalMessageTypeAfGzMlOxOrRq : Alpha 2
  deriving DecidableEq, Repr

namespace StandardAcknowledgement

def encode (message : StandardAcknowledgement) : List UInt8 :=
  OutgoingMessagesHeader.encode message.outgoingMessagesHeader
    ++ (Alpha.encode message.traderId
    ++ (Alpha.encode message.originalMessageTypeAfGzMlOxOrRq))

def decode (bytes : List UInt8) : Option (StandardAcknowledgement × List UInt8) := do
  let (outgoingMessagesHeader, bytes) ← OutgoingMessagesHeader.decode bytes
  let (traderId, bytes) ← Alpha.decode 8 bytes
  let (originalMessageTypeAfGzMlOxOrRq, bytes) ← Alpha.decode 2 bytes
  pure ({ outgoingMessagesHeader, traderId, originalMessageTypeAfGzMlOxOrRq }, bytes)

@[simp] theorem encode_length (message : StandardAcknowledgement) : (encode message).length = 32 := by
  unfold encode
  simp only [List.length_append, OutgoingMessagesHeader.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : StandardAcknowledgement) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : StandardAcknowledgement) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, OutgoingMessagesHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end StandardAcknowledgement

/-- Order Cancellation Acknowledgement: 126 bytes -/
structure OrderCancellationAcknowledgement where
  group : Alpha 2
  instrument : Alpha 4
  traderId : Alpha 8
  orderId : Alpha 8
  status : Alpha 1
  verbSide : Alpha 1
  quantity : Alpha 8
  assignedPrice : Alpha 10
  clearingData : ClearingData
  ownerData : OwnerData
  originalOrderId : Alpha 8
  filler6 : Alpha 6
  deriving DecidableEq, Repr

namespace OrderCancellationAcknowledgement

def encode (message : OrderCancellationAcknowledgement) : List UInt8 :=
  Alpha.encode message.group
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.traderId
    ++ (Alpha.encode message.orderId
    ++ (Alpha.encode message.status
    ++ (Alpha.encode message.verbSide
    ++ (Alpha.encode message.quantity
    ++ (Alpha.encode message.assignedPrice
    ++ (ClearingData.encode message.clearingData
    ++ (OwnerData.encode message.ownerData
    ++ (Alpha.encode message.originalOrderId
    ++ (Alpha.encode message.filler6)))))))))))

def decode (bytes : List UInt8) : Option (OrderCancellationAcknowledgement × List UInt8) := do
  let (group, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (traderId, bytes) ← Alpha.decode 8 bytes
  let (orderId, bytes) ← Alpha.decode 8 bytes
  let (status, bytes) ← Alpha.decode 1 bytes
  let (verbSide, bytes) ← Alpha.decode 1 bytes
  let (quantity, bytes) ← Alpha.decode 8 bytes
  let (assignedPrice, bytes) ← Alpha.decode 10 bytes
  let (clearingData, bytes) ← ClearingData.decode bytes
  let (ownerData, bytes) ← OwnerData.decode bytes
  let (originalOrderId, bytes) ← Alpha.decode 8 bytes
  let (filler6, bytes) ← Alpha.decode 6 bytes
  pure ({ group, instrument, traderId, orderId, status, verbSide, quantity, assignedPrice, clearingData, ownerData, originalOrderId, filler6 }, bytes)

@[simp] theorem encode_length (message : OrderCancellationAcknowledgement) : (encode message).length = 126 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, ClearingData.encode_length, OwnerData.encode_length]

theorem encode_length_pos (message : OrderCancellationAcknowledgement) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderCancellationAcknowledgement) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, ClearingData.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OwnerData.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderCancellationAcknowledgement

/-- Bulk Quote Acknowledgement Occurrence: 7 bytes -/
structure BulkQuoteAcknowledgementOccurrence where
  quoteNumber : Alpha 3
  errorCode : Alpha 4
  deriving DecidableEq, Repr

namespace BulkQuoteAcknowledgementOccurrence

def encode (message : BulkQuoteAcknowledgementOccurrence) : List UInt8 :=
  Alpha.encode message.quoteNumber
    ++ (Alpha.encode message.errorCode)

def decode (bytes : List UInt8) : Option (BulkQuoteAcknowledgementOccurrence × List UInt8) := do
  let (quoteNumber, bytes) ← Alpha.decode 3 bytes
  let (errorCode, bytes) ← Alpha.decode 4 bytes
  pure ({ quoteNumber, errorCode }, bytes)

@[simp] theorem encode_length (message : BulkQuoteAcknowledgementOccurrence) : (encode message).length = 7 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : BulkQuoteAcknowledgementOccurrence) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BulkQuoteAcknowledgementOccurrence) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end BulkQuoteAcknowledgementOccurrence

/-- Bulk Quote Acknowledgement -/
structure BulkQuoteAcknowledgement where
  outgoingMessagesHeader : OutgoingMessagesHeader
  group : Alpha 2
  quoteIdentifierOnThisGroup : Alpha 8
  bulkQuoteAcknowledgementOccurrence : Digited 3 BulkQuoteAcknowledgementOccurrence
  deriving DecidableEq, Repr

namespace BulkQuoteAcknowledgement

def encode (message : BulkQuoteAcknowledgement) : List UInt8 :=
  OutgoingMessagesHeader.encode message.outgoingMessagesHeader
    ++ (Alpha.encode message.group
    ++ (Alpha.encode message.quoteIdentifierOnThisGroup
    ++ (encodeDigits 3 message.bulkQuoteAcknowledgementOccurrence.val.length
    ++ (encodeMany BulkQuoteAcknowledgementOccurrence.encode message.bulkQuoteAcknowledgementOccurrence.val))))

def decode (bytes : List UInt8) : Option (BulkQuoteAcknowledgement × List UInt8) := do
  let (outgoingMessagesHeader, bytes) ← OutgoingMessagesHeader.decode bytes
  let (group, bytes) ← Alpha.decode 2 bytes
  let (quoteIdentifierOnThisGroup, bytes) ← Alpha.decode 8 bytes
  let (numberOfQuotesInError, bytes) ← decodeDigits 3 bytes
  let (bulkQuoteAcknowledgementOccurrence_, bytes) ← decodeMany BulkQuoteAcknowledgementOccurrence.decode numberOfQuotesInError bytes
  if fits_bulkQuoteAcknowledgementOccurrence : bulkQuoteAcknowledgementOccurrence_.length < 10 ^ 3 then
    pure ({ outgoingMessagesHeader, group, quoteIdentifierOnThisGroup, bulkQuoteAcknowledgementOccurrence := ⟨bulkQuoteAcknowledgementOccurrence_, fits_bulkQuoteAcknowledgementOccurrence⟩ }, bytes)
  else none

theorem encode_length_pos (message : BulkQuoteAcknowledgement) : (encode message).length > 0 := by
  unfold encode
  simp only [OutgoingMessagesHeader.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : BulkQuoteAcknowledgement) : (encode message).length ≤ 7028 := by
  have bound_bulkQuoteAcknowledgementOccurrence := message.bulkQuoteAcknowledgementOccurrence.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, OutgoingMessagesHeader.encode_length, Alpha.encode_length, encodeDigits_length, encodeMany_length_const BulkQuoteAcknowledgementOccurrence.encode 7 BulkQuoteAcknowledgementOccurrence.encode_length]
  omega

@[simp] theorem decode_encode (message : BulkQuoteAcknowledgement) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, OutgoingMessagesHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.bulkQuoteAcknowledgementOccurrence.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany BulkQuoteAcknowledgementOccurrence.encode BulkQuoteAcknowledgementOccurrence.decode BulkQuoteAcknowledgementOccurrence.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.bulkQuoteAcknowledgementOccurrence.length_lt]
  rfl

end BulkQuoteAcknowledgement

/-- Bulk Command Acknowledgement Occurrence: 8 bytes -/
structure BulkCommandAcknowledgementOccurrence where
  commandNumber : Alpha 4
  errorCode : Alpha 4
  deriving DecidableEq, Repr

namespace BulkCommandAcknowledgementOccurrence

def encode (message : BulkCommandAcknowledgementOccurrence) : List UInt8 :=
  Alpha.encode message.commandNumber
    ++ (Alpha.encode message.errorCode)

def decode (bytes : List UInt8) : Option (BulkCommandAcknowledgementOccurrence × List UInt8) := do
  let (commandNumber, bytes) ← Alpha.decode 4 bytes
  let (errorCode, bytes) ← Alpha.decode 4 bytes
  pure ({ commandNumber, errorCode }, bytes)

@[simp] theorem encode_length (message : BulkCommandAcknowledgementOccurrence) : (encode message).length = 8 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : BulkCommandAcknowledgementOccurrence) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : BulkCommandAcknowledgementOccurrence) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end BulkCommandAcknowledgementOccurrence

/-- Bulk Command Acknowledgement -/
structure BulkCommandAcknowledgement where
  outgoingMessagesHeader : OutgoingMessagesHeader
  bulkCommandAcknowledgementOccurrence : Digited 4 BulkCommandAcknowledgementOccurrence
  deriving DecidableEq, Repr

namespace BulkCommandAcknowledgement

def encode (message : BulkCommandAcknowledgement) : List UInt8 :=
  OutgoingMessagesHeader.encode message.outgoingMessagesHeader
    ++ (encodeDigits 4 message.bulkCommandAcknowledgementOccurrence.val.length
    ++ (encodeMany BulkCommandAcknowledgementOccurrence.encode message.bulkCommandAcknowledgementOccurrence.val))

def decode (bytes : List UInt8) : Option (BulkCommandAcknowledgement × List UInt8) := do
  let (outgoingMessagesHeader, bytes) ← OutgoingMessagesHeader.decode bytes
  let (numberOfCommands, bytes) ← decodeDigits 4 bytes
  let (bulkCommandAcknowledgementOccurrence_, bytes) ← decodeMany BulkCommandAcknowledgementOccurrence.decode numberOfCommands bytes
  if fits_bulkCommandAcknowledgementOccurrence : bulkCommandAcknowledgementOccurrence_.length < 10 ^ 4 then
    pure ({ outgoingMessagesHeader, bulkCommandAcknowledgementOccurrence := ⟨bulkCommandAcknowledgementOccurrence_, fits_bulkCommandAcknowledgementOccurrence⟩ }, bytes)
  else none

theorem encode_length_pos (message : BulkCommandAcknowledgement) : (encode message).length > 0 := by
  unfold encode
  simp only [OutgoingMessagesHeader.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : BulkCommandAcknowledgement) : (encode message).length ≤ 80018 := by
  have bound_bulkCommandAcknowledgementOccurrence := message.bulkCommandAcknowledgementOccurrence.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, OutgoingMessagesHeader.encode_length, encodeDigits_length, encodeMany_length_const BulkCommandAcknowledgementOccurrence.encode 8 BulkCommandAcknowledgementOccurrence.encode_length]
  omega

@[simp] theorem decode_encode (message : BulkCommandAcknowledgement) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, OutgoingMessagesHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.bulkCommandAcknowledgementOccurrence.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany BulkCommandAcknowledgementOccurrence.encode BulkCommandAcknowledgementOccurrence.decode BulkCommandAcknowledgementOccurrence.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.bulkCommandAcknowledgementOccurrence.length_lt]
  rfl

end BulkCommandAcknowledgement

/-- Risk Limits Usage Occurrence: 28 bytes -/
structure RiskLimitsUsageOccurrence where
  trader : Alpha 4
  group : Alpha 2
  usageStatus : Alpha 1
  limitType : Alpha 1
  currentUsage : Alpha 10
  limitValue : Alpha 10
  deriving DecidableEq, Repr

namespace RiskLimitsUsageOccurrence

def encode (message : RiskLimitsUsageOccurrence) : List UInt8 :=
  Alpha.encode message.trader
    ++ (Alpha.encode message.group
    ++ (Alpha.encode message.usageStatus
    ++ (Alpha.encode message.limitType
    ++ (Alpha.encode message.currentUsage
    ++ (Alpha.encode message.limitValue)))))

def decode (bytes : List UInt8) : Option (RiskLimitsUsageOccurrence × List UInt8) := do
  let (trader, bytes) ← Alpha.decode 4 bytes
  let (group, bytes) ← Alpha.decode 2 bytes
  let (usageStatus, bytes) ← Alpha.decode 1 bytes
  let (limitType, bytes) ← Alpha.decode 1 bytes
  let (currentUsage, bytes) ← Alpha.decode 10 bytes
  let (limitValue, bytes) ← Alpha.decode 10 bytes
  pure ({ trader, group, usageStatus, limitType, currentUsage, limitValue }, bytes)

@[simp] theorem encode_length (message : RiskLimitsUsageOccurrence) : (encode message).length = 28 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length]

theorem encode_length_pos (message : RiskLimitsUsageOccurrence) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RiskLimitsUsageOccurrence) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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

end RiskLimitsUsageOccurrence

/-- Risk Limits Usage -/
structure RiskLimitsUsage where
  outgoingMessagesHeader : OutgoingMessagesHeader
  riskLimitsUsageOccurrence : Digited 4 RiskLimitsUsageOccurrence
  deriving DecidableEq, Repr

namespace RiskLimitsUsage

def encode (message : RiskLimitsUsage) : List UInt8 :=
  OutgoingMessagesHeader.encode message.outgoingMessagesHeader
    ++ (encodeDigits 4 message.riskLimitsUsageOccurrence.val.length
    ++ (encodeMany RiskLimitsUsageOccurrence.encode message.riskLimitsUsageOccurrence.val))

def decode (bytes : List UInt8) : Option (RiskLimitsUsage × List UInt8) := do
  let (outgoingMessagesHeader, bytes) ← OutgoingMessagesHeader.decode bytes
  let (numberOfUsageBlocks, bytes) ← decodeDigits 4 bytes
  let (riskLimitsUsageOccurrence_, bytes) ← decodeMany RiskLimitsUsageOccurrence.decode numberOfUsageBlocks bytes
  if fits_riskLimitsUsageOccurrence : riskLimitsUsageOccurrence_.length < 10 ^ 4 then
    pure ({ outgoingMessagesHeader, riskLimitsUsageOccurrence := ⟨riskLimitsUsageOccurrence_, fits_riskLimitsUsageOccurrence⟩ }, bytes)
  else none

theorem encode_length_pos (message : RiskLimitsUsage) : (encode message).length > 0 := by
  unfold encode
  simp only [OutgoingMessagesHeader.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : RiskLimitsUsage) : (encode message).length ≤ 279998 := by
  have bound_riskLimitsUsageOccurrence := message.riskLimitsUsageOccurrence.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, OutgoingMessagesHeader.encode_length, encodeDigits_length, encodeMany_length_const RiskLimitsUsageOccurrence.encode 28 RiskLimitsUsageOccurrence.encode_length]
  omega

@[simp] theorem decode_encode (message : RiskLimitsUsage) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, OutgoingMessagesHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.riskLimitsUsageOccurrence.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany RiskLimitsUsageOccurrence.encode RiskLimitsUsageOccurrence.decode RiskLimitsUsageOccurrence.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.riskLimitsUsageOccurrence.length_lt]
  rfl

end RiskLimitsUsage

/-- Excluded Instrument Notice Occurrence: 4 bytes -/
structure ExcludedInstrumentNoticeOccurrence where
  instrument : Alpha 4
  deriving DecidableEq, Repr

namespace ExcludedInstrumentNoticeOccurrence

def encode (message : ExcludedInstrumentNoticeOccurrence) : List UInt8 :=
  Alpha.encode message.instrument

def decode (bytes : List UInt8) : Option (ExcludedInstrumentNoticeOccurrence × List UInt8) := do
  let (instrument, bytes) ← Alpha.decode 4 bytes
  pure ({ instrument }, bytes)

@[simp] theorem encode_length (message : ExcludedInstrumentNoticeOccurrence) : (encode message).length = 4 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : ExcludedInstrumentNoticeOccurrence) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ExcludedInstrumentNoticeOccurrence) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end ExcludedInstrumentNoticeOccurrence

/-- Excluded Instrument Notice -/
structure ExcludedInstrumentNotice where
  outgoingMessagesHeader : OutgoingMessagesHeader
  group : Alpha 2
  filler2 : Alpha 2
  traderId : Alpha 8
  filler4 : Alpha 4
  excludedInstrumentNoticeOccurrence : Digited 4 ExcludedInstrumentNoticeOccurrence
  deriving DecidableEq, Repr

namespace ExcludedInstrumentNotice

def encode (message : ExcludedInstrumentNotice) : List UInt8 :=
  OutgoingMessagesHeader.encode message.outgoingMessagesHeader
    ++ (Alpha.encode message.group
    ++ (Alpha.encode message.filler2
    ++ (Alpha.encode message.traderId
    ++ (Alpha.encode message.filler4
    ++ (encodeDigits 4 message.excludedInstrumentNoticeOccurrence.val.length
    ++ (encodeMany ExcludedInstrumentNoticeOccurrence.encode message.excludedInstrumentNoticeOccurrence.val))))))

def decode (bytes : List UInt8) : Option (ExcludedInstrumentNotice × List UInt8) := do
  let (outgoingMessagesHeader, bytes) ← OutgoingMessagesHeader.decode bytes
  let (group, bytes) ← Alpha.decode 2 bytes
  let (filler2, bytes) ← Alpha.decode 2 bytes
  let (traderId, bytes) ← Alpha.decode 8 bytes
  let (filler4, bytes) ← Alpha.decode 4 bytes
  let (nbOfInstruments, bytes) ← decodeDigits 4 bytes
  let (excludedInstrumentNoticeOccurrence_, bytes) ← decodeMany ExcludedInstrumentNoticeOccurrence.decode nbOfInstruments bytes
  if fits_excludedInstrumentNoticeOccurrence : excludedInstrumentNoticeOccurrence_.length < 10 ^ 4 then
    pure ({ outgoingMessagesHeader, group, filler2, traderId, filler4, excludedInstrumentNoticeOccurrence := ⟨excludedInstrumentNoticeOccurrence_, fits_excludedInstrumentNoticeOccurrence⟩ }, bytes)
  else none

theorem encode_length_pos (message : ExcludedInstrumentNotice) : (encode message).length > 0 := by
  unfold encode
  simp only [OutgoingMessagesHeader.encode_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ExcludedInstrumentNotice) : (encode message).length ≤ 40038 := by
  have bound_excludedInstrumentNoticeOccurrence := message.excludedInstrumentNoticeOccurrence.length_lt
  unfold encode
  simp only [List.length_append, ← Nat.add_assoc, OutgoingMessagesHeader.encode_length, Alpha.encode_length, encodeDigits_length, encodeMany_length_const ExcludedInstrumentNoticeOccurrence.encode 4 ExcludedInstrumentNoticeOccurrence.encode_length]
  omega

@[simp] theorem decode_encode (message : ExcludedInstrumentNotice) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, OutgoingMessagesHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, decodeDigits_encodeDigits _ _ message.excludedInstrumentNoticeOccurrence.length_lt, some_bind]
  dsimp only
  rw [decodeMany_encodeMany ExcludedInstrumentNoticeOccurrence.encode ExcludedInstrumentNoticeOccurrence.decode ExcludedInstrumentNoticeOccurrence.decode_encode, some_bind]
  dsimp only
  rw [dite_eq_left message.excludedInstrumentNoticeOccurrence.length_lt]
  rfl

end ExcludedInstrumentNotice

/-- Group State Change: 25 bytes -/
structure GroupStateChange where
  outgoingMessagesHeader : OutgoingMessagesHeader
  group : Alpha 2
  groupState : Alpha 1
  deriving DecidableEq, Repr

namespace GroupStateChange

def encode (message : GroupStateChange) : List UInt8 :=
  OutgoingMessagesHeader.encode message.outgoingMessagesHeader
    ++ (Alpha.encode message.group
    ++ (Alpha.encode message.groupState))

def decode (bytes : List UInt8) : Option (GroupStateChange × List UInt8) := do
  let (outgoingMessagesHeader, bytes) ← OutgoingMessagesHeader.decode bytes
  let (group, bytes) ← Alpha.decode 2 bytes
  let (groupState, bytes) ← Alpha.decode 1 bytes
  pure ({ outgoingMessagesHeader, group, groupState }, bytes)

@[simp] theorem encode_length (message : GroupStateChange) : (encode message).length = 25 := by
  unfold encode
  simp only [List.length_append, OutgoingMessagesHeader.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : GroupStateChange) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : GroupStateChange) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, OutgoingMessagesHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end GroupStateChange

/-- Instrument State Change: 29 bytes -/
structure InstrumentStateChange where
  outgoingMessagesHeader : OutgoingMessagesHeader
  group : Alpha 2
  instrument : Alpha 4
  instrumentState : Alpha 1
  deriving DecidableEq, Repr

namespace InstrumentStateChange

def encode (message : InstrumentStateChange) : List UInt8 :=
  OutgoingMessagesHeader.encode message.outgoingMessagesHeader
    ++ (Alpha.encode message.group
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.instrumentState)))

def decode (bytes : List UInt8) : Option (InstrumentStateChange × List UInt8) := do
  let (outgoingMessagesHeader, bytes) ← OutgoingMessagesHeader.decode bytes
  let (group, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (instrumentState, bytes) ← Alpha.decode 1 bytes
  pure ({ outgoingMessagesHeader, group, instrument, instrumentState }, bytes)

@[simp] theorem encode_length (message : InstrumentStateChange) : (encode message).length = 29 := by
  unfold encode
  simp only [List.length_append, OutgoingMessagesHeader.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : InstrumentStateChange) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : InstrumentStateChange) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, OutgoingMessagesHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end InstrumentStateChange

/-- Leg Execution Notice: 235 bytes -/
structure LegExecutionNotice where
  outgoingMessagesHeader : OutgoingMessagesHeader
  group : Alpha 2
  instrument : Alpha 4
  traderId : Alpha 8
  referenceIdOrderIdOrQuoteId : Alpha 8
  verbSide : Alpha 1
  quantityTraded : Alpha 8
  tradePrice : Alpha 10
  tradingEngineTimestampOfTheTradeLocalHhmmss : Alpha 6
  clearingData : ClearingData
  ownerData : OwnerData
  specialTradeIndicator : Alpha 1
  priceType : Alpha 1
  tradeType : Alpha 1
  filler6 : Alpha 6
  tradeNumber : Alpha 8
  tradeMemo : Alpha 50
  originalReferenceId : Alpha 8
  idCodeForTheCounterpartParticipant : Alpha 4
  strategyGroup : Alpha 2
  strategyInstrumentId : Alpha 4
  strategyVerbSide : Alpha 1
  strategyTradeNumber : Alpha 8
  legNumber : Alpha 2
  deriving DecidableEq, Repr

namespace LegExecutionNotice

def encode (message : LegExecutionNotice) : List UInt8 :=
  OutgoingMessagesHeader.encode message.outgoingMessagesHeader
    ++ (Alpha.encode message.group
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.traderId
    ++ (Alpha.encode message.referenceIdOrderIdOrQuoteId
    ++ (Alpha.encode message.verbSide
    ++ (Alpha.encode message.quantityTraded
    ++ (Alpha.encode message.tradePrice
    ++ (Alpha.encode message.tradingEngineTimestampOfTheTradeLocalHhmmss
    ++ (ClearingData.encode message.clearingData
    ++ (OwnerData.encode message.ownerData
    ++ (Alpha.encode message.specialTradeIndicator
    ++ (Alpha.encode message.priceType
    ++ (Alpha.encode message.tradeType
    ++ (Alpha.encode message.filler6
    ++ (Alpha.encode message.tradeNumber
    ++ (Alpha.encode message.tradeMemo
    ++ (Alpha.encode message.originalReferenceId
    ++ (Alpha.encode message.idCodeForTheCounterpartParticipant
    ++ (Alpha.encode message.strategyGroup
    ++ (Alpha.encode message.strategyInstrumentId
    ++ (Alpha.encode message.strategyVerbSide
    ++ (Alpha.encode message.strategyTradeNumber
    ++ (Alpha.encode message.legNumber)))))))))))))))))))))))

def decode (bytes : List UInt8) : Option (LegExecutionNotice × List UInt8) := do
  let (outgoingMessagesHeader, bytes) ← OutgoingMessagesHeader.decode bytes
  let (group, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (traderId, bytes) ← Alpha.decode 8 bytes
  let (referenceIdOrderIdOrQuoteId, bytes) ← Alpha.decode 8 bytes
  let (verbSide, bytes) ← Alpha.decode 1 bytes
  let (quantityTraded, bytes) ← Alpha.decode 8 bytes
  let (tradePrice, bytes) ← Alpha.decode 10 bytes
  let (tradingEngineTimestampOfTheTradeLocalHhmmss, bytes) ← Alpha.decode 6 bytes
  let (clearingData, bytes) ← ClearingData.decode bytes
  let (ownerData, bytes) ← OwnerData.decode bytes
  let (specialTradeIndicator, bytes) ← Alpha.decode 1 bytes
  let (priceType, bytes) ← Alpha.decode 1 bytes
  let (tradeType, bytes) ← Alpha.decode 1 bytes
  let (filler6, bytes) ← Alpha.decode 6 bytes
  let (tradeNumber, bytes) ← Alpha.decode 8 bytes
  let (tradeMemo, bytes) ← Alpha.decode 50 bytes
  let (originalReferenceId, bytes) ← Alpha.decode 8 bytes
  let (idCodeForTheCounterpartParticipant, bytes) ← Alpha.decode 4 bytes
  let (strategyGroup, bytes) ← Alpha.decode 2 bytes
  let (strategyInstrumentId, bytes) ← Alpha.decode 4 bytes
  let (strategyVerbSide, bytes) ← Alpha.decode 1 bytes
  let (strategyTradeNumber, bytes) ← Alpha.decode 8 bytes
  let (legNumber, bytes) ← Alpha.decode 2 bytes
  pure ({ outgoingMessagesHeader, group, instrument, traderId, referenceIdOrderIdOrQuoteId, verbSide, quantityTraded, tradePrice, tradingEngineTimestampOfTheTradeLocalHhmmss, clearingData, ownerData, specialTradeIndicator, priceType, tradeType, filler6, tradeNumber, tradeMemo, originalReferenceId, idCodeForTheCounterpartParticipant, strategyGroup, strategyInstrumentId, strategyVerbSide, strategyTradeNumber, legNumber }, bytes)

@[simp] theorem encode_length (message : LegExecutionNotice) : (encode message).length = 235 := by
  unfold encode
  simp only [List.length_append, OutgoingMessagesHeader.encode_length, Alpha.encode_length, ClearingData.encode_length, OwnerData.encode_length]

theorem encode_length_pos (message : LegExecutionNotice) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LegExecutionNotice) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, OutgoingMessagesHeader.decode_encode, some_bind]
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
  rw [List.append_assoc, ClearingData.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OwnerData.decode_encode, some_bind]
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

end LegExecutionNotice

/-- Counterpart Owner Data: 50 bytes -/
structure CounterpartOwnerData where
  memo : Alpha 50
  deriving DecidableEq, Repr

namespace CounterpartOwnerData

def encode (message : CounterpartOwnerData) : List UInt8 :=
  Alpha.encode message.memo

def decode (bytes : List UInt8) : Option (CounterpartOwnerData × List UInt8) := do
  let (memo, bytes) ← Alpha.decode 50 bytes
  pure ({ memo }, bytes)

@[simp] theorem encode_length (message : CounterpartOwnerData) : (encode message).length = 50 := by
  unfold encode
  simp only [Alpha.encode_length]

theorem encode_length_pos (message : CounterpartOwnerData) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CounterpartOwnerData) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [Alpha.decode_encode, some_bind]
  rfl

end CounterpartOwnerData

/-- Overstepped Order Or Quote Notice: 112 bytes -/
structure OversteppedOrderOrQuoteNotice where
  outgoingMessagesHeader : OutgoingMessagesHeader
  group : Alpha 2
  instrument : Alpha 4
  verb : Alpha 1
  orderType : Alpha 1
  traderId : Alpha 8
  orderId : Alpha 8
  counterpartTraderId : Alpha 8
  counterpartOrderId : Alpha 8
  counterpartOwnerData : CounterpartOwnerData
  deriving DecidableEq, Repr

namespace OversteppedOrderOrQuoteNotice

def encode (message : OversteppedOrderOrQuoteNotice) : List UInt8 :=
  OutgoingMessagesHeader.encode message.outgoingMessagesHeader
    ++ (Alpha.encode message.group
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.verb
    ++ (Alpha.encode message.orderType
    ++ (Alpha.encode message.traderId
    ++ (Alpha.encode message.orderId
    ++ (Alpha.encode message.counterpartTraderId
    ++ (Alpha.encode message.counterpartOrderId
    ++ (CounterpartOwnerData.encode message.counterpartOwnerData)))))))))

def decode (bytes : List UInt8) : Option (OversteppedOrderOrQuoteNotice × List UInt8) := do
  let (outgoingMessagesHeader, bytes) ← OutgoingMessagesHeader.decode bytes
  let (group, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (verb, bytes) ← Alpha.decode 1 bytes
  let (orderType, bytes) ← Alpha.decode 1 bytes
  let (traderId, bytes) ← Alpha.decode 8 bytes
  let (orderId, bytes) ← Alpha.decode 8 bytes
  let (counterpartTraderId, bytes) ← Alpha.decode 8 bytes
  let (counterpartOrderId, bytes) ← Alpha.decode 8 bytes
  let (counterpartOwnerData, bytes) ← CounterpartOwnerData.decode bytes
  pure ({ outgoingMessagesHeader, group, instrument, verb, orderType, traderId, orderId, counterpartTraderId, counterpartOrderId, counterpartOwnerData }, bytes)

@[simp] theorem encode_length (message : OversteppedOrderOrQuoteNotice) : (encode message).length = 112 := by
  unfold encode
  simp only [List.length_append, OutgoingMessagesHeader.encode_length, Alpha.encode_length, CounterpartOwnerData.encode_length]

theorem encode_length_pos (message : OversteppedOrderOrQuoteNotice) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OversteppedOrderOrQuoteNotice) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, OutgoingMessagesHeader.decode_encode, some_bind]
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
  rw [CounterpartOwnerData.decode_encode, some_bind]
  rfl

end OversteppedOrderOrQuoteNotice

/-- Cancellation Of All Quotes Notice: 37 bytes -/
structure CancellationOfAllQuotesNotice where
  outgoingMessagesHeader : OutgoingMessagesHeader
  group : Alpha 2
  instrument : Alpha 4
  traderId : Alpha 8
  cancelReason : Alpha 1
  deriving DecidableEq, Repr

namespace CancellationOfAllQuotesNotice

def encode (message : CancellationOfAllQuotesNotice) : List UInt8 :=
  OutgoingMessagesHeader.encode message.outgoingMessagesHeader
    ++ (Alpha.encode message.group
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.traderId
    ++ (Alpha.encode message.cancelReason))))

def decode (bytes : List UInt8) : Option (CancellationOfAllQuotesNotice × List UInt8) := do
  let (outgoingMessagesHeader, bytes) ← OutgoingMessagesHeader.decode bytes
  let (group, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (traderId, bytes) ← Alpha.decode 8 bytes
  let (cancelReason, bytes) ← Alpha.decode 1 bytes
  pure ({ outgoingMessagesHeader, group, instrument, traderId, cancelReason }, bytes)

@[simp] theorem encode_length (message : CancellationOfAllQuotesNotice) : (encode message).length = 37 := by
  unfold encode
  simp only [List.length_append, OutgoingMessagesHeader.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : CancellationOfAllQuotesNotice) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : CancellationOfAllQuotesNotice) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, OutgoingMessagesHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end CancellationOfAllQuotesNotice

/-- Execution Notice: 218 bytes -/
structure ExecutionNotice where
  outgoingMessagesHeader : OutgoingMessagesHeader
  group : Alpha 2
  instrument : Alpha 4
  traderId : Alpha 8
  referenceIdOrderIdOrQuoteId : Alpha 8
  verbSide : Alpha 1
  quantityTraded : Alpha 8
  tradePrice : Alpha 10
  tradingEngineTimestampOfTheTradeLocalHhmmss : Alpha 6
  clearingData : ClearingData
  ownerData : OwnerData
  specialTradeIndicator : Alpha 1
  priceType : Alpha 1
  tradeType : Alpha 1
  filler6 : Alpha 6
  tradeNumber : Alpha 8
  tradeMemo : Alpha 50
  originalReferenceId : Alpha 8
  idCodeForTheCounterpartParticipant : Alpha 4
  deriving DecidableEq, Repr

namespace ExecutionNotice

def encode (message : ExecutionNotice) : List UInt8 :=
  OutgoingMessagesHeader.encode message.outgoingMessagesHeader
    ++ (Alpha.encode message.group
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.traderId
    ++ (Alpha.encode message.referenceIdOrderIdOrQuoteId
    ++ (Alpha.encode message.verbSide
    ++ (Alpha.encode message.quantityTraded
    ++ (Alpha.encode message.tradePrice
    ++ (Alpha.encode message.tradingEngineTimestampOfTheTradeLocalHhmmss
    ++ (ClearingData.encode message.clearingData
    ++ (OwnerData.encode message.ownerData
    ++ (Alpha.encode message.specialTradeIndicator
    ++ (Alpha.encode message.priceType
    ++ (Alpha.encode message.tradeType
    ++ (Alpha.encode message.filler6
    ++ (Alpha.encode message.tradeNumber
    ++ (Alpha.encode message.tradeMemo
    ++ (Alpha.encode message.originalReferenceId
    ++ (Alpha.encode message.idCodeForTheCounterpartParticipant))))))))))))))))))

def decode (bytes : List UInt8) : Option (ExecutionNotice × List UInt8) := do
  let (outgoingMessagesHeader, bytes) ← OutgoingMessagesHeader.decode bytes
  let (group, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (traderId, bytes) ← Alpha.decode 8 bytes
  let (referenceIdOrderIdOrQuoteId, bytes) ← Alpha.decode 8 bytes
  let (verbSide, bytes) ← Alpha.decode 1 bytes
  let (quantityTraded, bytes) ← Alpha.decode 8 bytes
  let (tradePrice, bytes) ← Alpha.decode 10 bytes
  let (tradingEngineTimestampOfTheTradeLocalHhmmss, bytes) ← Alpha.decode 6 bytes
  let (clearingData, bytes) ← ClearingData.decode bytes
  let (ownerData, bytes) ← OwnerData.decode bytes
  let (specialTradeIndicator, bytes) ← Alpha.decode 1 bytes
  let (priceType, bytes) ← Alpha.decode 1 bytes
  let (tradeType, bytes) ← Alpha.decode 1 bytes
  let (filler6, bytes) ← Alpha.decode 6 bytes
  let (tradeNumber, bytes) ← Alpha.decode 8 bytes
  let (tradeMemo, bytes) ← Alpha.decode 50 bytes
  let (originalReferenceId, bytes) ← Alpha.decode 8 bytes
  let (idCodeForTheCounterpartParticipant, bytes) ← Alpha.decode 4 bytes
  pure ({ outgoingMessagesHeader, group, instrument, traderId, referenceIdOrderIdOrQuoteId, verbSide, quantityTraded, tradePrice, tradingEngineTimestampOfTheTradeLocalHhmmss, clearingData, ownerData, specialTradeIndicator, priceType, tradeType, filler6, tradeNumber, tradeMemo, originalReferenceId, idCodeForTheCounterpartParticipant }, bytes)

@[simp] theorem encode_length (message : ExecutionNotice) : (encode message).length = 218 := by
  unfold encode
  simp only [List.length_append, OutgoingMessagesHeader.encode_length, Alpha.encode_length, ClearingData.encode_length, OwnerData.encode_length]

theorem encode_length_pos (message : ExecutionNotice) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ExecutionNotice) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, OutgoingMessagesHeader.decode_encode, some_bind]
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
  rw [List.append_assoc, ClearingData.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OwnerData.decode_encode, some_bind]
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

end ExecutionNotice

/-- Execution Cancellation Notice: 196 bytes -/
structure ExecutionCancellationNotice where
  group : Alpha 2
  instrument : Alpha 4
  traderId : Alpha 8
  referenceIdOrderIdOrQuoteId : Alpha 8
  verbSide : Alpha 1
  quantityTraded : Alpha 8
  tradePrice : Alpha 10
  tradingEngineTimestampOfTheTradeLocalHhmmss : Alpha 6
  clearingData : ClearingData
  ownerData : OwnerData
  specialTradeIndicator : Alpha 1
  priceType : Alpha 1
  tradeType : Alpha 1
  filler6 : Alpha 6
  tradeNumber : Alpha 8
  tradeMemo : Alpha 50
  originalReferenceId : Alpha 8
  idCodeForTheCounterpartParticipant : Alpha 4
  deriving DecidableEq, Repr

namespace ExecutionCancellationNotice

def encode (message : ExecutionCancellationNotice) : List UInt8 :=
  Alpha.encode message.group
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.traderId
    ++ (Alpha.encode message.referenceIdOrderIdOrQuoteId
    ++ (Alpha.encode message.verbSide
    ++ (Alpha.encode message.quantityTraded
    ++ (Alpha.encode message.tradePrice
    ++ (Alpha.encode message.tradingEngineTimestampOfTheTradeLocalHhmmss
    ++ (ClearingData.encode message.clearingData
    ++ (OwnerData.encode message.ownerData
    ++ (Alpha.encode message.specialTradeIndicator
    ++ (Alpha.encode message.priceType
    ++ (Alpha.encode message.tradeType
    ++ (Alpha.encode message.filler6
    ++ (Alpha.encode message.tradeNumber
    ++ (Alpha.encode message.tradeMemo
    ++ (Alpha.encode message.originalReferenceId
    ++ (Alpha.encode message.idCodeForTheCounterpartParticipant)))))))))))))))))

def decode (bytes : List UInt8) : Option (ExecutionCancellationNotice × List UInt8) := do
  let (group, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (traderId, bytes) ← Alpha.decode 8 bytes
  let (referenceIdOrderIdOrQuoteId, bytes) ← Alpha.decode 8 bytes
  let (verbSide, bytes) ← Alpha.decode 1 bytes
  let (quantityTraded, bytes) ← Alpha.decode 8 bytes
  let (tradePrice, bytes) ← Alpha.decode 10 bytes
  let (tradingEngineTimestampOfTheTradeLocalHhmmss, bytes) ← Alpha.decode 6 bytes
  let (clearingData, bytes) ← ClearingData.decode bytes
  let (ownerData, bytes) ← OwnerData.decode bytes
  let (specialTradeIndicator, bytes) ← Alpha.decode 1 bytes
  let (priceType, bytes) ← Alpha.decode 1 bytes
  let (tradeType, bytes) ← Alpha.decode 1 bytes
  let (filler6, bytes) ← Alpha.decode 6 bytes
  let (tradeNumber, bytes) ← Alpha.decode 8 bytes
  let (tradeMemo, bytes) ← Alpha.decode 50 bytes
  let (originalReferenceId, bytes) ← Alpha.decode 8 bytes
  let (idCodeForTheCounterpartParticipant, bytes) ← Alpha.decode 4 bytes
  pure ({ group, instrument, traderId, referenceIdOrderIdOrQuoteId, verbSide, quantityTraded, tradePrice, tradingEngineTimestampOfTheTradeLocalHhmmss, clearingData, ownerData, specialTradeIndicator, priceType, tradeType, filler6, tradeNumber, tradeMemo, originalReferenceId, idCodeForTheCounterpartParticipant }, bytes)

@[simp] theorem encode_length (message : ExecutionCancellationNotice) : (encode message).length = 196 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, ClearingData.encode_length, OwnerData.encode_length]

theorem encode_length_pos (message : ExecutionCancellationNotice) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : ExecutionCancellationNotice) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, ClearingData.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OwnerData.decode_encode, some_bind]
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

end ExecutionCancellationNotice

/-- Leg Execution Cancellation Notice: 213 bytes -/
structure LegExecutionCancellationNotice where
  group : Alpha 2
  instrument : Alpha 4
  traderId : Alpha 8
  referenceIdOrderIdOrQuoteId : Alpha 8
  verbSide : Alpha 1
  quantityTraded : Alpha 8
  tradePrice : Alpha 10
  tradingEngineTimestampOfTheTradeLocalHhmmss : Alpha 6
  clearingData : ClearingData
  ownerData : OwnerData
  specialTradeIndicator : Alpha 1
  priceType : Alpha 1
  tradeType : Alpha 1
  filler6 : Alpha 6
  tradeNumber : Alpha 8
  tradeMemo : Alpha 50
  originalReferenceId : Alpha 8
  idCodeForTheCounterpartParticipant : Alpha 4
  strategyGroup : Alpha 2
  strategyInstrumentId : Alpha 4
  strategyVerbSide : Alpha 1
  strategyTradeNumber : Alpha 8
  legNumber : Alpha 2
  deriving DecidableEq, Repr

namespace LegExecutionCancellationNotice

def encode (message : LegExecutionCancellationNotice) : List UInt8 :=
  Alpha.encode message.group
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.traderId
    ++ (Alpha.encode message.referenceIdOrderIdOrQuoteId
    ++ (Alpha.encode message.verbSide
    ++ (Alpha.encode message.quantityTraded
    ++ (Alpha.encode message.tradePrice
    ++ (Alpha.encode message.tradingEngineTimestampOfTheTradeLocalHhmmss
    ++ (ClearingData.encode message.clearingData
    ++ (OwnerData.encode message.ownerData
    ++ (Alpha.encode message.specialTradeIndicator
    ++ (Alpha.encode message.priceType
    ++ (Alpha.encode message.tradeType
    ++ (Alpha.encode message.filler6
    ++ (Alpha.encode message.tradeNumber
    ++ (Alpha.encode message.tradeMemo
    ++ (Alpha.encode message.originalReferenceId
    ++ (Alpha.encode message.idCodeForTheCounterpartParticipant
    ++ (Alpha.encode message.strategyGroup
    ++ (Alpha.encode message.strategyInstrumentId
    ++ (Alpha.encode message.strategyVerbSide
    ++ (Alpha.encode message.strategyTradeNumber
    ++ (Alpha.encode message.legNumber))))))))))))))))))))))

def decode (bytes : List UInt8) : Option (LegExecutionCancellationNotice × List UInt8) := do
  let (group, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (traderId, bytes) ← Alpha.decode 8 bytes
  let (referenceIdOrderIdOrQuoteId, bytes) ← Alpha.decode 8 bytes
  let (verbSide, bytes) ← Alpha.decode 1 bytes
  let (quantityTraded, bytes) ← Alpha.decode 8 bytes
  let (tradePrice, bytes) ← Alpha.decode 10 bytes
  let (tradingEngineTimestampOfTheTradeLocalHhmmss, bytes) ← Alpha.decode 6 bytes
  let (clearingData, bytes) ← ClearingData.decode bytes
  let (ownerData, bytes) ← OwnerData.decode bytes
  let (specialTradeIndicator, bytes) ← Alpha.decode 1 bytes
  let (priceType, bytes) ← Alpha.decode 1 bytes
  let (tradeType, bytes) ← Alpha.decode 1 bytes
  let (filler6, bytes) ← Alpha.decode 6 bytes
  let (tradeNumber, bytes) ← Alpha.decode 8 bytes
  let (tradeMemo, bytes) ← Alpha.decode 50 bytes
  let (originalReferenceId, bytes) ← Alpha.decode 8 bytes
  let (idCodeForTheCounterpartParticipant, bytes) ← Alpha.decode 4 bytes
  let (strategyGroup, bytes) ← Alpha.decode 2 bytes
  let (strategyInstrumentId, bytes) ← Alpha.decode 4 bytes
  let (strategyVerbSide, bytes) ← Alpha.decode 1 bytes
  let (strategyTradeNumber, bytes) ← Alpha.decode 8 bytes
  let (legNumber, bytes) ← Alpha.decode 2 bytes
  pure ({ group, instrument, traderId, referenceIdOrderIdOrQuoteId, verbSide, quantityTraded, tradePrice, tradingEngineTimestampOfTheTradeLocalHhmmss, clearingData, ownerData, specialTradeIndicator, priceType, tradeType, filler6, tradeNumber, tradeMemo, originalReferenceId, idCodeForTheCounterpartParticipant, strategyGroup, strategyInstrumentId, strategyVerbSide, strategyTradeNumber, legNumber }, bytes)

@[simp] theorem encode_length (message : LegExecutionCancellationNotice) : (encode message).length = 213 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, ClearingData.encode_length, OwnerData.encode_length]

theorem encode_length_pos (message : LegExecutionCancellationNotice) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : LegExecutionCancellationNotice) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, ClearingData.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OwnerData.decode_encode, some_bind]
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

end LegExecutionCancellationNotice

/-- Order Cancellation Notice By Mod Or System: 126 bytes -/
structure OrderCancellationNoticeByModOrSystem where
  group : Alpha 2
  instrument : Alpha 4
  traderId : Alpha 8
  orderId : Alpha 8
  status : Alpha 1
  verbSide : Alpha 1
  quantity : Alpha 8
  assignedPrice : Alpha 10
  clearingData : ClearingData
  ownerData : OwnerData
  originalOrderId : Alpha 8
  filler6 : Alpha 6
  deriving DecidableEq, Repr

namespace OrderCancellationNoticeByModOrSystem

def encode (message : OrderCancellationNoticeByModOrSystem) : List UInt8 :=
  Alpha.encode message.group
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.traderId
    ++ (Alpha.encode message.orderId
    ++ (Alpha.encode message.status
    ++ (Alpha.encode message.verbSide
    ++ (Alpha.encode message.quantity
    ++ (Alpha.encode message.assignedPrice
    ++ (ClearingData.encode message.clearingData
    ++ (OwnerData.encode message.ownerData
    ++ (Alpha.encode message.originalOrderId
    ++ (Alpha.encode message.filler6)))))))))))

def decode (bytes : List UInt8) : Option (OrderCancellationNoticeByModOrSystem × List UInt8) := do
  let (group, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (traderId, bytes) ← Alpha.decode 8 bytes
  let (orderId, bytes) ← Alpha.decode 8 bytes
  let (status, bytes) ← Alpha.decode 1 bytes
  let (verbSide, bytes) ← Alpha.decode 1 bytes
  let (quantity, bytes) ← Alpha.decode 8 bytes
  let (assignedPrice, bytes) ← Alpha.decode 10 bytes
  let (clearingData, bytes) ← ClearingData.decode bytes
  let (ownerData, bytes) ← OwnerData.decode bytes
  let (originalOrderId, bytes) ← Alpha.decode 8 bytes
  let (filler6, bytes) ← Alpha.decode 6 bytes
  pure ({ group, instrument, traderId, orderId, status, verbSide, quantity, assignedPrice, clearingData, ownerData, originalOrderId, filler6 }, bytes)

@[simp] theorem encode_length (message : OrderCancellationNoticeByModOrSystem) : (encode message).length = 126 := by
  unfold encode
  simp only [List.length_append, Alpha.encode_length, ClearingData.encode_length, OwnerData.encode_length]

theorem encode_length_pos (message : OrderCancellationNoticeByModOrSystem) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : OrderCancellationNoticeByModOrSystem) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
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
  rw [List.append_assoc, ClearingData.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, OwnerData.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end OrderCancellationNoticeByModOrSystem

/-- Request For Quote With Side Acknowledgement: 37 bytes -/
structure RequestForQuoteWithSideAcknowledgement where
  outgoingMessagesHeader : OutgoingMessagesHeader
  group : Alpha 2
  instrument : Alpha 4
  quantity : Alpha 8
  marketSide : Alpha 1
  deriving DecidableEq, Repr

namespace RequestForQuoteWithSideAcknowledgement

def encode (message : RequestForQuoteWithSideAcknowledgement) : List UInt8 :=
  OutgoingMessagesHeader.encode message.outgoingMessagesHeader
    ++ (Alpha.encode message.group
    ++ (Alpha.encode message.instrument
    ++ (Alpha.encode message.quantity
    ++ (Alpha.encode message.marketSide))))

def decode (bytes : List UInt8) : Option (RequestForQuoteWithSideAcknowledgement × List UInt8) := do
  let (outgoingMessagesHeader, bytes) ← OutgoingMessagesHeader.decode bytes
  let (group, bytes) ← Alpha.decode 2 bytes
  let (instrument, bytes) ← Alpha.decode 4 bytes
  let (quantity, bytes) ← Alpha.decode 8 bytes
  let (marketSide, bytes) ← Alpha.decode 1 bytes
  pure ({ outgoingMessagesHeader, group, instrument, quantity, marketSide }, bytes)

@[simp] theorem encode_length (message : RequestForQuoteWithSideAcknowledgement) : (encode message).length = 37 := by
  unfold encode
  simp only [List.length_append, OutgoingMessagesHeader.encode_length, Alpha.encode_length]

theorem encode_length_pos (message : RequestForQuoteWithSideAcknowledgement) : (encode message).length > 0 := by
  rw [encode_length]
  decide

@[simp] theorem decode_encode (message : RequestForQuoteWithSideAcknowledgement) (rest : List UInt8) :
    decode (encode message ++ rest) = some (message, rest) := by
  unfold decode encode
  rw [List.append_assoc, OutgoingMessagesHeader.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [List.append_assoc, Alpha.decode_encode, some_bind]
  dsimp only
  rw [Alpha.decode_encode, some_bind]
  rfl

end RequestForQuoteWithSideAcknowledgement

/-- Any Exchange Message, selected by Message Type -/
inductive ExchangeMessage where
  | connectionAcknowledgement (message : ConnectionAcknowledgement) -- "TK" 0x544B
  | disconnectionInstructionAcknowledgement (message : DisconnectionInstructionAcknowledgement) -- "TM" 0x544D
  | heartbeatQuestion (message : HeartbeatQuestion) -- "TH" 0x5448
  | outOfSequence (message : OutOfSequence) -- "TO" 0x544F
  | technicalErrorNotice (message : TechnicalErrorNotice) -- "TE" 0x5445
  | disconnectionAcknowledgement (message : DisconnectionAcknowledgement) -- "TL" 0x544C
  | endOfTransmission (message : EndOfTransmission) -- "TT" 0x5454
  | orderReply (message : OrderReply) -- "AE" 0x4145
  | errorNotice (message : ErrorNotice) -- "ER" 0x4552
  | bulkQuoteDataAcknowledgement (message : BulkQuoteDataAcknowledgement) -- "KD" 0x4B44
  | orderAcknowledgement (message : OrderAcknowledgement) -- "KE" 0x4B45
  | globalCancellationConfirmation (message : GlobalCancellationConfirmation) -- "KG" 0x4B47
  | orderModificationAcknowledgement (message : OrderModificationAcknowledgement) -- "KM" 0x4B4D
  | newStrategyInstrumentAcknowledgement (message : NewStrategyInstrumentAcknowledgement) -- "KN" 0x4B4E
  | standardAcknowledgement (message : StandardAcknowledgement) -- "KO" 0x4B4F
  | orderCancellationAcknowledgement (message : OrderCancellationAcknowledgement) -- "KZ" 0x4B5A
  | bulkQuoteAcknowledgement (message : BulkQuoteAcknowledgement) -- "LA" 0x4C41
  | bulkCommandAcknowledgement (message : BulkCommandAcknowledgement) -- "LB" 0x4C42
  | riskLimitsUsage (message : RiskLimitsUsage) -- "MN" 0x4D4E
  | excludedInstrumentNotice (message : ExcludedInstrumentNotice) -- "NE" 0x4E45
  | groupStateChange (message : GroupStateChange) -- "NG" 0x4E47
  | instrumentStateChange (message : InstrumentStateChange) -- "NI" 0x4E49
  | legExecutionNotice (message : LegExecutionNotice) -- "NL" 0x4E4C
  | oversteppedOrderOrQuoteNotice (message : OversteppedOrderOrQuoteNotice) -- "NO" 0x4E4F
  | cancellationOfAllQuotesNotice (message : CancellationOfAllQuotesNotice) -- "NP" 0x4E50
  | executionNotice (message : ExecutionNotice) -- "NT" 0x4E54
  | executionCancellationNotice (message : ExecutionCancellationNotice) -- "NX" 0x4E58
  | legExecutionCancellationNotice (message : LegExecutionCancellationNotice) -- "NY" 0x4E59
  | orderCancellationNoticeByModOrSystem (message : OrderCancellationNoticeByModOrSystem) -- "NZ" 0x4E5A
  | requestForQuoteWithSideAcknowledgement (message : RequestForQuoteWithSideAcknowledgement) -- "QW" 0x5157
  deriving DecidableEq, Repr

namespace ExchangeMessage

/-- The Message Type each message is sent under -/
def tag : ExchangeMessage → BitVec 16
  | .connectionAcknowledgement _ => 21579
  | .disconnectionInstructionAcknowledgement _ => 21581
  | .heartbeatQuestion _ => 21576
  | .outOfSequence _ => 21583
  | .technicalErrorNotice _ => 21573
  | .disconnectionAcknowledgement _ => 21580
  | .endOfTransmission _ => 21588
  | .orderReply _ => 16709
  | .errorNotice _ => 17746
  | .bulkQuoteDataAcknowledgement _ => 19268
  | .orderAcknowledgement _ => 19269
  | .globalCancellationConfirmation _ => 19271
  | .orderModificationAcknowledgement _ => 19277
  | .newStrategyInstrumentAcknowledgement _ => 19278
  | .standardAcknowledgement _ => 19279
  | .orderCancellationAcknowledgement _ => 19290
  | .bulkQuoteAcknowledgement _ => 19521
  | .bulkCommandAcknowledgement _ => 19522
  | .riskLimitsUsage _ => 19790
  | .excludedInstrumentNotice _ => 20037
  | .groupStateChange _ => 20039
  | .instrumentStateChange _ => 20041
  | .legExecutionNotice _ => 20044
  | .oversteppedOrderOrQuoteNotice _ => 20047
  | .cancellationOfAllQuotesNotice _ => 20048
  | .executionNotice _ => 20052
  | .executionCancellationNotice _ => 20056
  | .legExecutionCancellationNotice _ => 20057
  | .orderCancellationNoticeByModOrSystem _ => 20058
  | .requestForQuoteWithSideAcknowledgement _ => 20823

def encode : ExchangeMessage → List UInt8
  | .connectionAcknowledgement message => ConnectionAcknowledgement.encode message
  | .disconnectionInstructionAcknowledgement message => DisconnectionInstructionAcknowledgement.encode message
  | .heartbeatQuestion message => HeartbeatQuestion.encode message
  | .outOfSequence message => OutOfSequence.encode message
  | .technicalErrorNotice message => TechnicalErrorNotice.encode message
  | .disconnectionAcknowledgement message => DisconnectionAcknowledgement.encode message
  | .endOfTransmission message => EndOfTransmission.encode message
  | .orderReply message => OrderReply.encode message
  | .errorNotice message => ErrorNotice.encode message
  | .bulkQuoteDataAcknowledgement message => BulkQuoteDataAcknowledgement.encode message
  | .orderAcknowledgement message => OrderAcknowledgement.encode message
  | .globalCancellationConfirmation message => GlobalCancellationConfirmation.encode message
  | .orderModificationAcknowledgement message => OrderModificationAcknowledgement.encode message
  | .newStrategyInstrumentAcknowledgement message => NewStrategyInstrumentAcknowledgement.encode message
  | .standardAcknowledgement message => StandardAcknowledgement.encode message
  | .orderCancellationAcknowledgement message => OrderCancellationAcknowledgement.encode message
  | .bulkQuoteAcknowledgement message => BulkQuoteAcknowledgement.encode message
  | .bulkCommandAcknowledgement message => BulkCommandAcknowledgement.encode message
  | .riskLimitsUsage message => RiskLimitsUsage.encode message
  | .excludedInstrumentNotice message => ExcludedInstrumentNotice.encode message
  | .groupStateChange message => GroupStateChange.encode message
  | .instrumentStateChange message => InstrumentStateChange.encode message
  | .legExecutionNotice message => LegExecutionNotice.encode message
  | .oversteppedOrderOrQuoteNotice message => OversteppedOrderOrQuoteNotice.encode message
  | .cancellationOfAllQuotesNotice message => CancellationOfAllQuotesNotice.encode message
  | .executionNotice message => ExecutionNotice.encode message
  | .executionCancellationNotice message => ExecutionCancellationNotice.encode message
  | .legExecutionCancellationNotice message => LegExecutionCancellationNotice.encode message
  | .orderCancellationNoticeByModOrSystem message => OrderCancellationNoticeByModOrSystem.encode message
  | .requestForQuoteWithSideAcknowledgement message => RequestForQuoteWithSideAcknowledgement.encode message

/-- The most bytes any message's encoding can take -/
theorem encode_length_le (message : ExchangeMessage) : (encode message).length ≤ 279998 := by
  cases message with
  | connectionAcknowledgement inner =>
    simp only [encode, ConnectionAcknowledgement.encode_length]
    omega
  | disconnectionInstructionAcknowledgement inner =>
    simp only [encode, DisconnectionInstructionAcknowledgement.encode_length]
    omega
  | heartbeatQuestion inner =>
    simp only [encode, HeartbeatQuestion.encode_length]
    omega
  | outOfSequence inner =>
    simp only [encode, OutOfSequence.encode_length]
    omega
  | technicalErrorNotice inner =>
    simp only [encode, TechnicalErrorNotice.encode_length]
    omega
  | disconnectionAcknowledgement inner =>
    simp only [encode, DisconnectionAcknowledgement.encode_length]
    omega
  | endOfTransmission inner =>
    simp only [encode, EndOfTransmission.encode_length]
    omega
  | orderReply inner =>
    simp only [encode, OrderReply.encode_length]
    omega
  | errorNotice inner =>
    simp only [encode, ErrorNotice.encode_length]
    omega
  | bulkQuoteDataAcknowledgement inner =>
    simp only [encode, BulkQuoteDataAcknowledgement.encode_length]
    omega
  | orderAcknowledgement inner =>
    simp only [encode, OrderAcknowledgement.encode_length]
    omega
  | globalCancellationConfirmation inner =>
    simp only [encode, GlobalCancellationConfirmation.encode_length]
    omega
  | orderModificationAcknowledgement inner =>
    simp only [encode, OrderModificationAcknowledgement.encode_length]
    omega
  | newStrategyInstrumentAcknowledgement inner =>
    have bound_inner := NewStrategyInstrumentAcknowledgement.encode_length_le inner
    simp only [encode]
    omega
  | standardAcknowledgement inner =>
    simp only [encode, StandardAcknowledgement.encode_length]
    omega
  | orderCancellationAcknowledgement inner =>
    simp only [encode, OrderCancellationAcknowledgement.encode_length]
    omega
  | bulkQuoteAcknowledgement inner =>
    have bound_inner := BulkQuoteAcknowledgement.encode_length_le inner
    simp only [encode]
    omega
  | bulkCommandAcknowledgement inner =>
    have bound_inner := BulkCommandAcknowledgement.encode_length_le inner
    simp only [encode]
    omega
  | riskLimitsUsage inner =>
    have bound_inner := RiskLimitsUsage.encode_length_le inner
    simp only [encode]
    omega
  | excludedInstrumentNotice inner =>
    have bound_inner := ExcludedInstrumentNotice.encode_length_le inner
    simp only [encode]
    omega
  | groupStateChange inner =>
    simp only [encode, GroupStateChange.encode_length]
    omega
  | instrumentStateChange inner =>
    simp only [encode, InstrumentStateChange.encode_length]
    omega
  | legExecutionNotice inner =>
    simp only [encode, LegExecutionNotice.encode_length]
    omega
  | oversteppedOrderOrQuoteNotice inner =>
    simp only [encode, OversteppedOrderOrQuoteNotice.encode_length]
    omega
  | cancellationOfAllQuotesNotice inner =>
    simp only [encode, CancellationOfAllQuotesNotice.encode_length]
    omega
  | executionNotice inner =>
    simp only [encode, ExecutionNotice.encode_length]
    omega
  | executionCancellationNotice inner =>
    simp only [encode, ExecutionCancellationNotice.encode_length]
    omega
  | legExecutionCancellationNotice inner =>
    simp only [encode, LegExecutionCancellationNotice.encode_length]
    omega
  | orderCancellationNoticeByModOrSystem inner =>
    simp only [encode, OrderCancellationNoticeByModOrSystem.encode_length]
    omega
  | requestForQuoteWithSideAcknowledgement inner =>
    simp only [encode, RequestForQuoteWithSideAcknowledgement.encode_length]
    omega

def decode (tag : BitVec 16) (bytes : List UInt8) : Option (ExchangeMessage × List UInt8) :=
  if tag = 21579 then (ConnectionAcknowledgement.decode bytes).map fun (message, rest) => (.connectionAcknowledgement message, rest)
  else if tag = 21581 then (DisconnectionInstructionAcknowledgement.decode bytes).map fun (message, rest) => (.disconnectionInstructionAcknowledgement message, rest)
  else if tag = 21576 then (HeartbeatQuestion.decode bytes).map fun (message, rest) => (.heartbeatQuestion message, rest)
  else if tag = 21583 then (OutOfSequence.decode bytes).map fun (message, rest) => (.outOfSequence message, rest)
  else if tag = 21573 then (TechnicalErrorNotice.decode bytes).map fun (message, rest) => (.technicalErrorNotice message, rest)
  else if tag = 21580 then (DisconnectionAcknowledgement.decode bytes).map fun (message, rest) => (.disconnectionAcknowledgement message, rest)
  else if tag = 21588 then (EndOfTransmission.decode bytes).map fun (message, rest) => (.endOfTransmission message, rest)
  else if tag = 16709 then (OrderReply.decode bytes).map fun (message, rest) => (.orderReply message, rest)
  else if tag = 17746 then (ErrorNotice.decode bytes).map fun (message, rest) => (.errorNotice message, rest)
  else if tag = 19268 then (BulkQuoteDataAcknowledgement.decode bytes).map fun (message, rest) => (.bulkQuoteDataAcknowledgement message, rest)
  else if tag = 19269 then (OrderAcknowledgement.decode bytes).map fun (message, rest) => (.orderAcknowledgement message, rest)
  else if tag = 19271 then (GlobalCancellationConfirmation.decode bytes).map fun (message, rest) => (.globalCancellationConfirmation message, rest)
  else if tag = 19277 then (OrderModificationAcknowledgement.decode bytes).map fun (message, rest) => (.orderModificationAcknowledgement message, rest)
  else if tag = 19278 then (NewStrategyInstrumentAcknowledgement.decode bytes).map fun (message, rest) => (.newStrategyInstrumentAcknowledgement message, rest)
  else if tag = 19279 then (StandardAcknowledgement.decode bytes).map fun (message, rest) => (.standardAcknowledgement message, rest)
  else if tag = 19290 then (OrderCancellationAcknowledgement.decode bytes).map fun (message, rest) => (.orderCancellationAcknowledgement message, rest)
  else if tag = 19521 then (BulkQuoteAcknowledgement.decode bytes).map fun (message, rest) => (.bulkQuoteAcknowledgement message, rest)
  else if tag = 19522 then (BulkCommandAcknowledgement.decode bytes).map fun (message, rest) => (.bulkCommandAcknowledgement message, rest)
  else if tag = 19790 then (RiskLimitsUsage.decode bytes).map fun (message, rest) => (.riskLimitsUsage message, rest)
  else if tag = 20037 then (ExcludedInstrumentNotice.decode bytes).map fun (message, rest) => (.excludedInstrumentNotice message, rest)
  else if tag = 20039 then (GroupStateChange.decode bytes).map fun (message, rest) => (.groupStateChange message, rest)
  else if tag = 20041 then (InstrumentStateChange.decode bytes).map fun (message, rest) => (.instrumentStateChange message, rest)
  else if tag = 20044 then (LegExecutionNotice.decode bytes).map fun (message, rest) => (.legExecutionNotice message, rest)
  else if tag = 20047 then (OversteppedOrderOrQuoteNotice.decode bytes).map fun (message, rest) => (.oversteppedOrderOrQuoteNotice message, rest)
  else if tag = 20048 then (CancellationOfAllQuotesNotice.decode bytes).map fun (message, rest) => (.cancellationOfAllQuotesNotice message, rest)
  else if tag = 20052 then (ExecutionNotice.decode bytes).map fun (message, rest) => (.executionNotice message, rest)
  else if tag = 20056 then (ExecutionCancellationNotice.decode bytes).map fun (message, rest) => (.executionCancellationNotice message, rest)
  else if tag = 20057 then (LegExecutionCancellationNotice.decode bytes).map fun (message, rest) => (.legExecutionCancellationNotice message, rest)
  else if tag = 20058 then (OrderCancellationNoticeByModOrSystem.decode bytes).map fun (message, rest) => (.orderCancellationNoticeByModOrSystem message, rest)
  else if tag = 20823 then (RequestForQuoteWithSideAcknowledgement.decode bytes).map fun (message, rest) => (.requestForQuoteWithSideAcknowledgement message, rest)
  else none

@[simp] theorem decode_encode (message : ExchangeMessage) (rest : List UInt8) :
    decode (tag message) (encode message ++ rest) = some (message, rest) := by
  cases message <;> simp [decode, encode, tag]

end ExchangeMessage

/-- Exchange Packet -/
structure ExchangePacket where
  messageLength : BitVec 32
  exchangeMessage : ExchangeMessage
  endOfText : BitVec 8
  alignmentPadding : Capped 3
  deriving DecidableEq, Repr

namespace ExchangePacket

def encode (message : ExchangePacket) : List UInt8 :=
  encodeUIntLE 4 message.messageLength
    ++ (encodeUInt 2 (ExchangeMessage.tag message.exchangeMessage)
    ++ (ExchangeMessage.encode message.exchangeMessage
    ++ (encodeUInt 1 message.endOfText
    ++ (message.alignmentPadding.val))))

def decode (bytes : List UInt8) : Option ExchangePacket := do
  let (messageLength, bytes) ← decodeUIntLE 4 bytes
  let (messageType, bytes) ← decodeUInt 2 bytes
  let (exchangeMessage, bytes) ← ExchangeMessage.decode messageType bytes
  let (endOfText, bytes) ← decodeUInt 1 bytes
  let alignmentPadding_ := bytes
  if fits_alignmentPadding : alignmentPadding_.length ≤ 3 then
    pure { messageLength, exchangeMessage, endOfText, alignmentPadding := ⟨alignmentPadding_, fits_alignmentPadding⟩ }
  else none

theorem encode_length_pos (message : ExchangePacket) : (encode message).length > 0 := by
  unfold encode
  simp only [encodeUIntLE_length, List.length_append, ← Nat.add_assoc]
  omega

/-- The most bytes an encoding can take -/
theorem encode_length_le (message : ExchangePacket) : (encode message).length ≤ 280008 := by
  have bound_alignmentPadding := message.alignmentPadding.length_le
  unfold encode
  cases message.exchangeMessage with
  | connectionAcknowledgement inner =>
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, ConnectionAcknowledgement.encode_length]
    omega
  | disconnectionInstructionAcknowledgement inner =>
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, DisconnectionInstructionAcknowledgement.encode_length]
    omega
  | heartbeatQuestion inner =>
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, HeartbeatQuestion.encode_length]
    omega
  | outOfSequence inner =>
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, OutOfSequence.encode_length]
    omega
  | technicalErrorNotice inner =>
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, TechnicalErrorNotice.encode_length]
    omega
  | disconnectionAcknowledgement inner =>
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, DisconnectionAcknowledgement.encode_length]
    omega
  | endOfTransmission inner =>
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, EndOfTransmission.encode_length]
    omega
  | orderReply inner =>
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, OrderReply.encode_length]
    omega
  | errorNotice inner =>
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, ErrorNotice.encode_length]
    omega
  | bulkQuoteDataAcknowledgement inner =>
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, BulkQuoteDataAcknowledgement.encode_length]
    omega
  | orderAcknowledgement inner =>
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, OrderAcknowledgement.encode_length]
    omega
  | globalCancellationConfirmation inner =>
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, GlobalCancellationConfirmation.encode_length]
    omega
  | orderModificationAcknowledgement inner =>
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, OrderModificationAcknowledgement.encode_length]
    omega
  | newStrategyInstrumentAcknowledgement inner =>
    have bound_inner := NewStrategyInstrumentAcknowledgement.encode_length_le inner
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length]
    omega
  | standardAcknowledgement inner =>
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, StandardAcknowledgement.encode_length]
    omega
  | orderCancellationAcknowledgement inner =>
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, OrderCancellationAcknowledgement.encode_length]
    omega
  | bulkQuoteAcknowledgement inner =>
    have bound_inner := BulkQuoteAcknowledgement.encode_length_le inner
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length]
    omega
  | bulkCommandAcknowledgement inner =>
    have bound_inner := BulkCommandAcknowledgement.encode_length_le inner
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length]
    omega
  | riskLimitsUsage inner =>
    have bound_inner := RiskLimitsUsage.encode_length_le inner
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length]
    omega
  | excludedInstrumentNotice inner =>
    have bound_inner := ExcludedInstrumentNotice.encode_length_le inner
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length]
    omega
  | groupStateChange inner =>
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, GroupStateChange.encode_length]
    omega
  | instrumentStateChange inner =>
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, InstrumentStateChange.encode_length]
    omega
  | legExecutionNotice inner =>
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, LegExecutionNotice.encode_length]
    omega
  | oversteppedOrderOrQuoteNotice inner =>
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, OversteppedOrderOrQuoteNotice.encode_length]
    omega
  | cancellationOfAllQuotesNotice inner =>
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, CancellationOfAllQuotesNotice.encode_length]
    omega
  | executionNotice inner =>
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, ExecutionNotice.encode_length]
    omega
  | executionCancellationNotice inner =>
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, ExecutionCancellationNotice.encode_length]
    omega
  | legExecutionCancellationNotice inner =>
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, LegExecutionCancellationNotice.encode_length]
    omega
  | orderCancellationNoticeByModOrSystem inner =>
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, OrderCancellationNoticeByModOrSystem.encode_length]
    omega
  | requestForQuoteWithSideAcknowledgement inner =>
    simp only [ExchangeMessage.encode, List.length_append, ← Nat.add_assoc, encodeUIntLE_length, encodeUInt_length, RequestForQuoteWithSideAcknowledgement.encode_length]
    omega

theorem decode_encode (message : ExchangePacket) : decode (encode message) = some message := by
  unfold decode encode
  rw [decodeUIntLE_encodeUIntLE, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [ExchangeMessage.decode_encode, some_bind]
  dsimp only
  rw [decodeUInt_encodeUInt, some_bind]
  dsimp only
  rw [dite_eq_left message.alignmentPadding.length_le]
  rfl

end ExchangePacket

end Omi.TmxMxSolaorderentrySailV121Exchange
