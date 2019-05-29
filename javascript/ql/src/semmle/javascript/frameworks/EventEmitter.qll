// Provides superclasses for working with event emitters
// Much of this code is based off the current SocketIO.qll library, but eventually this more
// general model will be included into the class hierarchy in SocketIO, cutting down on the
// code duplication that this is currently introducing
import javascript

/**
 * Provides predicates for working with Node.js `EventEmitter`s.
 *  This is taken directly from the SocketIO library, and will be adapted
 */
private module EventEmitter {
  /** Gets the name of a method on `EventEmitter` that returns `this`. */
  string chainableMethod() {
    result = "off" or
    result = "removeAllListeners" or
    result = "removeListener" or
    result = "setMaxListeners" or
    result = on()
  }

  /** Gets the name of a method on `EventEmitter` that registers an event handler. */
  string on() {
    result = "addListener" or
    result = "on" or
    result = "once" or
    result = "prependListener" or
    result = "prependOnceListener"
  }

  abstract class Range extends DataFlow::Node { }

  private class DefaultRange extends Range {
    DefaultRange() {
      exists(DataFlow::MethodCallNode mcn |
        mcn.getCalleeName() = EventEmitter::on() and mcn.getReceiver() = this
      )
    }
  }
}

class EventEmitter extends DataFlow::SourceNode {
  EventEmitter::Range self;

  EventEmitter() { this = self }
}

// based on the SocketNode from the SocketIO library
class BaseNode extends DataFlow::SourceNode, EventEmitter { }

// based on the ReceiveNode from the SocketIO library
// note: took out the predicates for getting the arguments other than the event and the listener
// but they're in the SocketIO lib if needed in the general case later
class ListenNode extends DataFlow::MethodCallNode {
  BaseNode base;

  ListenNode() { this = base.getAMethodCall(EventEmitter::on()) }

  BaseNode getBase() { result = base }

  // get the event name associated with the data, if it can be determined
  string getEventName() { getArgument(0).mayHaveStringValue(result) }

  // get the callback that handles data received from a client
  DataFlow::FunctionNode getListener() { result = getCallback(1) }
}

// based on the SendNode from SocketIO
class EmitNode extends DataFlow::MethodCallNode {
  BaseNode base;

  int firstDataIndex;

  EmitNode() {
    exists(string m | this = base.getAMethodCall(m) |
      // a call to `emit`
      m = "emit" and
      firstDataIndex = 1
    )
  }

  BaseNode getBase() { result = base }

  // get the event name associated with the data, if it can be determined
  string getEventName() {
    if firstDataIndex = 1 then getArgument(0).mayHaveStringValue(result) else result = "message"
  }

  // get a listener if there is one
  // note: if this gets out of hand, i removed the concept of namespaces but we might have to add it back later
  ListenNode getAListener() { not result.getEventName() != getEventName() }
}

// naive code to debug with
class NaiveListenNode extends DataFlow::MethodCallNode {
  NaiveListenNode() { this.getCalleeName() = EventEmitter::on() }
}
