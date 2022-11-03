Require Import Coq.Init.Datatypes.
Require Import Coq.Lists.List.
Import ListNotations.

Module Nondeterminism.
  Record t (A : Type) := mk { ahead : list A;
                                       behind : list A;
                                       default : A; }.

  Definition Decider {A : Type} (s : t A) : (t A * A) :=
    match ahead A s with
      [] => let rev_behind := List.rev (behind A s) in
            match rev_behind with
              [] => (mk A [] [] (default A s), default A s)
            | h::t => (mk A t (h::[]) (default A s), h)
            end
    | h::t => (mk A t (h::(behind A s)) (default A s), h)
    end.

  Definition init {A : Type} (pattern : list A) (default_val : A)
    : t A :=
    mk A pattern [] default_val.
            
    

  Fixpoint ToListN {A : Type} (s : t A) (n : nat) : list A :=
    match n with
    | 0 => []
    | S p =>
        let '(s, a) := Decider s in
        a :: (ToListN s p)
    end.

  Example test_repeats
    : ToListN (init [1; 2; 3] 4) 7 = [1; 2; 3; 1; 2; 3; 1].
  Proof.
    simpl.
    reflexivity.
  Qed.

  Example test_defaults : ToListN (init [] 4) 3 = [4; 4; 4].
  Proof.
    simpl.
    reflexivity.
  Qed.
End Nondeterminism.

Module Countdown.
  Record t :=
    mk { starting : nat; current : nat }.

  Definition init (starting_val : nat) : t :=
    {| starting := starting_val;
      current := starting_val |}.

  Definition reset (countdown : t) : t :=
    init (starting countdown).
      
  Definition decrement
    (countdown : t) (decrement_val : nat) : t :=
    {| starting := starting countdown;
      current := (current countdown) - decrement_val |}.

  Search (nat -> nat -> bool).

  Definition at_zero
    (countdown : t)
    : bool :=
    Nat.eqb (current countdown) 0.

  Example test_init1 : at_zero (init 0) = true.
  Proof.
    simpl.
    reflexivity.
  Qed.

  Example test_init2 : at_zero (init 1) = false.
  Proof.
    simpl.
    reflexivity.
  Qed.

  Example test_decr1 : forall x y : nat, x - y = 0 -> at_zero (decrement (init x) y) = true.
  Proof.
    intros x y H.
    unfold init.
    unfold decrement.
    unfold at_zero.
    unfold current.
    rewrite H.
    simpl.
    reflexivity.
  Qed.

  Example test_decr2 : at_zero (decrement (init 5) 3) = false.
  Proof.
    simpl.
    reflexivity.
  Qed.

  Example test_decr3 : at_zero (decrement (decrement (init 5) 3) 3) = true.
  Proof.
    simpl.
    reflexivity.
  Qed.

  Example test_reset : at_zero (decrement (reset (decrement (init 5) 3)) 3) = false.
  Proof.
    simpl.
    reflexivity.
  Qed.
End Countdown.

Module Name.
  Inductive t :=
    Sender
  | Receiver.

  
  Definition eq_dec : forall x y : t, {x = y} + {x <> y}.
    decide equality.
  Defined.
End Name.

Module Seq.  
  Inductive t :=
    Zero
  | One.
  Definition eq_dec : forall x y : t, {x = y} + {x <> y}.
    decide equality.
  Defined.

  Definition flip (t : t) :=
    match t with
    | Zero => One
    | One => Zero
    end.

  Definition eq (a b : t) :=
    match (a, b) with
    | (Zero, Zero) | (One, One) => true
    | (_, _) => false
    end.
End Seq.

Module Packet.
  Definition t := nat.
  Definition eq_dec : forall x y : t, {x = y} + {x <> y}.
    decide equality.
  Defined.
End Packet.

Module Msg.
  Inductive t : Type :=
    Send : Packet.t -> Seq.t -> t
  | Ack : Seq.t -> t.
  Definition eq_dec : forall x y : t, {x = y} + {x <> y}.
    decide equality.
    - (* Seq *)
      apply Seq.eq_dec.
    - (* Packet *)
      apply Packet.eq_dec.
    - (* Seq *)
      apply Seq.eq_dec.
  Defined.
End Msg.

Module SendOrDrop.
  Inductive t :=
  | Send
  | Drop.
  Definition eq_dec
    : forall x y : t, {x = y} + {x <> y}.
    decide equality.
  Defined.
End SendOrDrop.


Module Input.
  Module ToSender.
    Inductive t : Type :=
      Packet : Packet.t -> t.
    Definition eq_dec
      : forall x y : t, {x = y} + {x <> y}.
      decide equality.
      - (* UserToSender *)
        apply Packet.eq_dec.
    Defined.
  End ToSender.
  
  Module ToReceiver.
    Inductive t : Type := .
    Definition eq_dec
      : forall x y : t, {x = y} + {x <> y}.
      decide equality.
    Defined.
  End ToReceiver.

  Module ToNetwork.    
    Inductive t := .
    Definition eq_dec
      : forall x y : t, {x = y} + {x <> y}.
      decide equality.
    Defined.
  End ToNetwork.

  Inductive t :=
    Sender : ToSender.t -> t
  | Receiver : ToReceiver.t -> t
  | Network : ToNetwork.t -> t
  | Poll : t.
  Definition eq_dec : forall x y : t, {x = y} + {x <> y}.
    decide equality.
    - (* Sender *)
      apply ToSender.eq_dec.
    - (* Receiver *)
      apply ToReceiver.eq_dec.
    - (* Network *)
      apply ToNetwork.eq_dec.
  Defined.

  Definition packet (n : nat) :=
    Sender (ToSender.Packet n).

End Input.

Module Output.
  Module FromSender.
    Inductive t :=
      Reject : Packet.t -> t.
    Definition eq_dec : forall x y : t, {x = y} + {x <> y}.
      decide equality.
      - (* Packet *)
        apply Packet.eq_dec.
    Defined.
  End FromSender.

  Module FromReceiver.
    Inductive t :=
      Success : Packet.t -> t.
    Definition eq_dec : forall x y : t, {x = y} + {x <> y}.
      decide equality.
      - (* Packet *)
        apply Packet.eq_dec.
    Defined.
  End FromReceiver.

  Inductive t :=
    SenderOutput : FromSender.t -> t
  | ReceiverOutput : FromReceiver.t -> t.
  (*| Debug : -> t.*)
  Definition eq_dec : forall x y : t, {x = y} + {x <> y}.
    decide equality.
    - (* FromSender *)
      apply FromSender.eq_dec.
    - (* FromReceiver *)
      apply FromReceiver.eq_dec.
  Defined.
End Output.

Module State.
  Module Sender.
    Record t
      := mk { sent_unacked : option Packet.t;
              timeout : Countdown.t;
              seq : Seq.t;
              outgoing : list Msg.t}.

    Definition init (timeout_val : nat) : t :=
      mk None (Countdown.init timeout_val) Seq.Zero [].

    Definition append_outgoing
      (sender : t) (additional_outgoing : list Msg.t)
      : t :=
      {| sent_unacked := sent_unacked sender;
        timeout := timeout sender;
        seq := seq sender;
        outgoing := (outgoing sender) ++ additional_outgoing |}.

    Definition set_sent_unacked_reset_timer
      (sender : t) (packet : Packet.t)
      : t :=
      {| sent_unacked := Some packet;
        timeout := Countdown.reset (timeout sender);
        seq := seq sender;
        outgoing := outgoing sender |}.

    Definition flip_seq
      (sender : t)
      : t :=
      {| sent_unacked := sent_unacked sender;
        timeout := timeout sender;
        seq := Seq.flip (seq sender);
        outgoing := outgoing sender |}.

    Definition flush_outgoing
      (sender : t)
      : list Msg.t * t :=
      (outgoing sender,
        {| sent_unacked := sent_unacked sender;
          timeout := timeout sender;
          seq := seq sender;
          outgoing := [] |}).

    Definition decrement_timeout
      (sender : t) (decrement_val : nat)
      : t :=
      {| sent_unacked := sent_unacked sender;
        timeout := Countdown.decrement (timeout sender) decrement_val;
        seq := seq sender;
        outgoing := outgoing sender |}.
          
      
    Definition timeout_expired
      (sender : t)
      : bool :=
      Countdown.at_zero (timeout sender).

    Definition receive_ack
      (sender : t) (ack_seq : Seq.t)
      : t :=
      match Seq.eq ack_seq (seq sender) with
          | true =>
              {| sent_unacked := None;
                timeout := Countdown.reset (timeout sender);
                seq := Seq.flip ack_seq;
                outgoing := outgoing sender |}
          | false =>
              sender
      end.

    
    Definition update_by_poll
      (sender : t)
      : list Output.t * t :=
      match sent_unacked sender with
      | None =>
          ([], sender)
      | Some in_flight =>
          let seq := seq sender in
          let sender_timeout_decr :=
            decrement_timeout
              sender
              1 in
          match timeout_expired sender_timeout_decr with
          | true =>
              let sender_timeout_reset :=
                set_sent_unacked_reset_timer
                  sender
                  in_flight in
              let message := Msg.Send in_flight seq in
              let sender :=
                append_outgoing
                  sender_timeout_reset
                  [message] in
              ([],
                sender)
          | false =>
              ([],
                sender_timeout_decr)
          end
      end.

    
    Definition poll
      (sender : t)
      : list Output.t * list Msg.t * t :=
      let (outputs, sender) := update_by_poll sender in
      let (outgoing, sender) := flush_outgoing sender in
      (outputs, outgoing, sender).
  
    
    Definition handle_message
      (sender : t) (message : Msg.t)
      : list Output.t * t :=
      match message with
      | Msg.Send _ _ => ([], sender)
      | Msg.Ack ack_seq =>
          ([], receive_ack sender ack_seq)
      end.

    Fixpoint rec_handle_messages
      (sender : t) (messages : list Msg.t) (accum_outputs : list Output.t)
      : list Output.t * t :=
      match messages with
      | [] => (accum_outputs, sender)
      | first::rest =>
          let '(additional_outputs, sender) :=
            handle_message sender first in
          rec_handle_messages
            sender
            rest
            (accum_outputs ++ additional_outputs)
      end.

    Definition handle_messages
      (sender : t) (messages : list Msg.t)
      : list Output.t * t :=
      rec_handle_messages sender messages [].

    Definition handle_input
      (sender : t) (input : Input.ToSender.t)
      : list Output.t * t :=
      let seq := seq sender in
      match input with
      | Input.ToSender.Packet packet =>
          match sent_unacked sender with
          | None =>
              let messages := [Msg.Send packet seq] in
              let sender := append_outgoing sender messages in
              let sender := set_sent_unacked_reset_timer sender packet in
              ([], sender)
          | Some in_flight =>
              ([Output.SenderOutput (Output.FromSender.Reject packet)],
                sender)
          end
      end.
  End Sender.

  Module Receiver.
    Record t
      := mk { seq : Seq.t;
              outgoing : list Msg.t}.
    
    Definition init : t :=
      mk Seq.Zero [].

    Definition append_outgoing
      (receiver : t) (additional_outgoing : list Msg.t)
      : t :=
      {| seq := seq receiver;
        outgoing := (outgoing receiver) ++ additional_outgoing |}.

    Definition flip_seq
      (receiver : t)
      : t :=
      {| seq := Seq.flip (seq receiver);
        outgoing := outgoing receiver |}.

    Definition flush_outgoing
      (receiver : t)
      : list Msg.t * t :=
      (outgoing receiver,
        {| seq := seq receiver;
          outgoing := [] |}).

    Definition update_by_poll
      (receiver : t)
      : list Output.t * t :=
      ([], receiver).

    Definition poll
      (receiver : t)
      : list Output.t * list Msg.t * t :=
      let (outputs, receiver) := update_by_poll receiver in
      let (outgoing, receiver) := flush_outgoing receiver in
      (outputs, outgoing, receiver).

    Definition handle_message
      (receiver : t) (message : Msg.t)
      : list Output.t * t :=
      match message with
      | Msg.Ack _ => ([], receiver)
      | Msg.Send packet packet_seq =>
          let outputs :=
            match Seq.eq packet_seq (seq receiver) with
            | true =>
                [Output.ReceiverOutput
                   (Output.FromReceiver.Success packet)]
            | false => []
            end
          in
          let outgoing := Msg.Ack packet_seq::(outgoing receiver) in
          (outputs, mk (Seq.flip packet_seq) outgoing)
      end.

    
    Fixpoint rec_handle_messages
      (receiver : t)
      (messages : list Msg.t)
      (accum_outputs : list Output.t)
      : list Output.t * t :=
      match messages with
      | [] => (accum_outputs, receiver)
      | first::rest =>
          let '(additional_outputs, receiver) :=
            handle_message receiver first in
          rec_handle_messages
            receiver
            rest
            (accum_outputs ++ additional_outputs)
      end.

    Definition handle_messages
      (receiver : t) (messages : list Msg.t)
      : list Output.t * t :=
      rec_handle_messages receiver messages [].

    Definition handle_input
      (receiver : t) (input : Input.ToReceiver.t)
      : list Output.t * t :=
      ([], receiver).  
  End Receiver.

  Module Network.
    Module NodeSpecific.
      Record t
        := mk { in_network : list Msg.t;
                drop_decider : Nondeterminism.t SendOrDrop.t;
                delay_decider : Nondeterminism.t Countdown.t;
                next_delay : Countdown.t}.
      
      Definition init
        (drop_pattern : list SendOrDrop.t) (delay_pattern : list nat)
        : t :=
        let delay_pattern :=
          List.map (fun delay => Countdown.init delay) delay_pattern in
        let delay_decider :=
          Nondeterminism.init delay_pattern (Countdown.init 0) in
        let (delay_decider, next_delay) :=
          Nondeterminism.Decider delay_decider in
        mk
          []
          (Nondeterminism.init drop_pattern SendOrDrop.Send)
          delay_decider
          next_delay.
      
      Fixpoint decide_on_messages
        (accum_outputs : list Output.t)
        (accum_outgoing : list Msg.t)
        (in_network : list Msg.t)
        (drop_decider : Nondeterminism.t SendOrDrop.t)
        (delay_decider : Nondeterminism.t Countdown.t)
        (next_delay : Countdown.t)
        : list Output.t * list Msg.t * t :=
        match in_network with
        | [] =>
            (accum_outputs, accum_outgoing,
              mk in_network drop_decider delay_decider next_delay)
        | head_packet::tail_packets =>
            match Countdown.at_zero next_delay with
            | true =>
                let (delay_decider, next_delay) :=
                  Nondeterminism.Decider delay_decider in
                let (drop_decider, next_decision) :=
                  Nondeterminism.Decider drop_decider in
                let accum_outgoing :=        
                  match next_decision with
                  | SendOrDrop.Send => accum_outgoing ++ [head_packet]
                  | SendOrDrop.Drop => accum_outgoing
                  end in
                decide_on_messages
                  accum_outputs
                  accum_outgoing
                  tail_packets
                  drop_decider
                  delay_decider
                  next_delay
            | false =>
                (accum_outputs, accum_outgoing,
                  mk in_network drop_decider delay_decider next_delay)
            end
        end.

      Definition poll
        (network : t)
        : list Output.t * list Msg.t * t :=
        let '(outputs, messages, network) :=
          let accum_outputs := [] in
          let accum_outgoing := [] in
          decide_on_messages
            accum_outputs
            accum_outgoing
            (in_network network)
            (drop_decider network)
            (delay_decider network)
            (next_delay network) in
        match in_network network with
        | [] => (outputs, messages, network)
        | _ => 
            (outputs,
              messages,
              {| in_network := in_network network;
                drop_decider := drop_decider network;
                delay_decider := delay_decider network;
                next_delay :=
                  Countdown.decrement (next_delay network) 1 |})
        end.


      Definition handle_messages
        (network : t) (messages : list Msg.t)
        : list Output.t * t :=
        ([],
          {| in_network := (in_network network) ++ messages;
            drop_decider := drop_decider network;
            delay_decider := delay_decider network;
            next_delay := next_delay network |}).


      Definition handle_input
        (network : t) (input : Input.ToNetwork.t)
        : list Output.t * t :=
        ([], network).

    End NodeSpecific.

    Record t
      := mk { sender_network : NodeSpecific.t;
              receiver_network : NodeSpecific.t}.

    Definition init
      (drop_patterns : Name.t -> list SendOrDrop.t)
      (delay_patterns : Name.t -> list nat)
      : t :=
      {| sender_network :=
          NodeSpecific.init
            (drop_patterns Name.Sender)
            (delay_patterns Name.Sender);
        receiver_network :=
          NodeSpecific.init
            (drop_patterns Name.Receiver)
            (delay_patterns Name.Receiver) |}.

    Definition poll
      (network : t)
      : list Output.t * (list Msg.t * list Msg.t) * t :=
      let '(sender_outputs, sender_messages, sender_net) :=
        NodeSpecific.poll (sender_network network) in
      let '(receiver_outputs, receiver_messages, receiver_net) :=
        NodeSpecific.poll (receiver_network network) in
      (sender_outputs ++ receiver_outputs,
        (sender_messages, receiver_messages),
        {| sender_network := sender_net;
          receiver_network := receiver_net |}).

    Definition handle_messages
      (network : t) (recipient : Name.t) (messages : list Msg.t)
      : list Output.t * t :=
      let '(outputs, sender_net, receiver_net) :=
        match recipient with
        | Name.Sender =>
            let '(sender_outputs, sender_net) :=
              NodeSpecific.handle_messages
                (sender_network network)
                messages in
            (sender_outputs, sender_net, (receiver_network network))
        | Name.Receiver =>
            let '(receiver_outputs, receiver_net) :=
              NodeSpecific.handle_messages
                (receiver_network network)
                messages in
            (receiver_outputs, (sender_network network), receiver_net)
        end in
      (outputs,
        {| sender_network := sender_net;
          receiver_network := receiver_net |}).

    Definition handle_input
      (network : t) (input : Input.ToNetwork.t)
      : list Output.t * t :=
      ([], network).



  End Network.
End State.


Module StopAndWait.
(*  Fixpoint rec_feed_messages_ends
    (sender : State.Sender.t) (receiver : State.Receiver.t)
    (messages : list (Msg.t * Name.t)) (accum_output : list Output.t)
    : (list Output.t * State.Sender.t * State.Receiver.t) :=
    match messages with
    | [] => (accum_output, sender, receiver)
    | message::tail =>
        let '(additional_output, sender, receiver) :=
          match message with
          | (content, Name.Sender) =>
              let '(sender_output, sender) :=
                State.Sender.handle_message
                  sender
                  content in
              (sender_output, sender, receiver)
                
          | (content, Name.Receiver) =>
              let '(receiver_output, receiver) :=
                State.Receiver.handle_message
                  receiver
                  content in
              (receiver_output, sender, receiver)
          end in
        rec_feed_messages_ends
          sender
          receiver
          tail
          (accum_output ++ additional_output)
    end.

  Definition feed_messages_ends
    (sender : State.Sender.t) (receiver : State.Receiver.t)
    (messages : list (Msg.t * Name.t))
    : (list Output.t * State.Sender.t * State.Receiver.t) :=
    rec_feed_messages_ends sender receiver messages [].
*)
  Fixpoint rec_simulate
    (steps : nat)
    (inputs : Nondeterminism.t Input.t)
    (sender : State.Sender.t)
    (receiver : State.Receiver.t)
    (network : State.Network.t)
    (accum_output : list Output.t)
    : (State.Sender.t * State.Receiver.t * State.Network.t * list Output.t) :=
    match steps with
    | 0 => (sender, receiver, network, accum_output)
    | S p =>
        let '(inputs, input) := Nondeterminism.Decider inputs in
        let '(sender, receiver, network, outputs) :=
          match input with
          | Input.Sender in_to_sender =>
              let '(sender_output, sender) :=
                State.Sender.handle_input sender in_to_sender in
              (sender, receiver, network, sender_output)
                
          | Input.Receiver in_to_receiver =>
              let '(receiver_output, receiver) :=
                State.Receiver.handle_input receiver in_to_receiver in
              (sender, receiver, network, receiver_output)
                
          | Input.Network in_to_network =>
              let '(network_output, network) :=
                State.Network.handle_input network in_to_network in
              (sender, receiver, network, network_output)
                
          | Input.Poll =>
              let '(outputs_poll_sender, from_sender, sender) :=
                State.Sender.poll sender in
              let '(outputs_poll_receiver, from_receiver, receiver) :=
                State.Receiver.poll receiver in
              let '(outputs_poll_network,
                      (to_receiver, to_sender), network) :=
                State.Network.poll network in
              let '(outputs_feed_sender, sender) :=
                State.Sender.handle_messages sender to_sender in
              let '(outputs_feed_receiver, receiver) :=
                State.Receiver.handle_messages receiver to_receiver in
              let '(outputs_sender_feed_network, network) :=
                State.Network.handle_messages
                  network
                  Name.Sender
                  from_sender in
              let '(outputs_receiver_feed_network, network) :=
                State.Network.handle_messages
                  network
                  Name.Receiver
                  from_receiver in
              (sender, receiver, network,
                outputs_poll_sender ++
                  outputs_poll_receiver ++
                  outputs_poll_network ++
                  outputs_feed_sender ++
                  outputs_feed_receiver ++
                  outputs_sender_feed_network ++
                  outputs_receiver_feed_network)
          end in
        rec_simulate
          p
          inputs
          sender receiver network
          (accum_output ++ outputs)
    end.
  

  Definition pack {T : Type}
    (sender_part : T) (receiver_part : T) (name : Name.t) :=
    match name with
    | Name.Sender => sender_part
    | Name.Receiver => receiver_part
    end.
            
               
  

  Definition simulate
    (steps : nat)
    (inputs : list Input.t)
    (sender_drop_pattern : list SendOrDrop.t)
    (receiver_drop_pattern : list SendOrDrop.t)
    (sender_delay_pattern : list nat)
    (receiver_delay_pattern : list nat)
    (sender_timeout : nat) :
    (State.Sender.t *
       State.Receiver.t *
       State.Network.t *
       list Output.t) :=
    let sender_start := State.Sender.init sender_timeout in
    let receiver_start := State.Receiver.init in
    let network_start :=
      State.Network.init
        (pack sender_drop_pattern receiver_drop_pattern)
        (pack sender_delay_pattern receiver_delay_pattern) in
    let inputs := Nondeterminism.init inputs Input.Poll in
    rec_simulate
      steps inputs sender_start receiver_start network_start [].

End StopAndWait.

Module SuccessfulSend.

  
  Definition packet := Input.packet.
  Definition poll := Input.Poll.

  Definition steps := 3.
  Definition inputs := [poll; poll].
  Definition sender_drop_pattern : list SendOrDrop.t := [].
  Definition receiver_drop_pattern : list SendOrDrop.t := [].
  Definition sender_delay_pattern : list nat := [].
  Definition receiver_delay_pattern : list nat := [].
  Definition sender_timeout := 5.

  Definition result (packet_val : nat) :=
    StopAndWait.simulate
      steps
      ((packet packet_val)::inputs)
      sender_drop_pattern
      receiver_drop_pattern
      sender_delay_pattern
      receiver_delay_pattern
      sender_timeout.

  
  Compute result 5.

 (* Definition result_sender :=
    State.Sender.mk
      (Some 5)
      (Countdown.decrement (Countdown.init 5) 2)
      Seq.Zero
      [].

  Definition result_receiver :=
    State.Receiver.mk
      Seq.One
      [Msg.Ack Seq.Zero].

  Definition result_network :=
    State.Network.mk
      (State.Network.NodeSpecific.mk
         []
   *)      

  Lemma sends_1 :
    forall packet_val, exists sender, exists receiver, exists network,
    result packet_val =
      (sender, receiver, network, [Output.ReceiverOutput (Output.FromReceiver.Success packet_val)]).
  Proof.
    intro packet_val.
    unfold result.
    unfold StopAndWait.simulate.
    unfold StopAndWait.rec_simulate.
    
