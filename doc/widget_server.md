# Documentation for server protocol for widgets.

The purpose of this file is to act as a reference for developers of Lean 3 editor extensions.
This is compatible with lean `v3.18.x` onwards.

## Useful reference sourcefiles:

- https://github.com/leanprover/lean-client-js/blob/master/lean-client-js-core/src/commands.ts
- https://github.com/leanprover-community/lean/blob/master/src/shell/server.cpp
- https://github.com/leanprover/vscode-lean/blob/master/infoview/widget.tsx
- https://github.com/leanprover-community/lean/blob/master/library/init/meta/widget/basic.lean

# Server protocol

The `lean` executable can be started in a server mode. To do this, pass the `--server` option.
The following arguments are also available:

- `--memory`, `-M` set the maximum amount of memory that should be used by Lean (in megabytes)
- `--timeout`, `-T` maximum number of memory allocations per task. This is a deterministic way of interrupting long running tasks.
- `--threads`, `-j`   number of threads used to process lean files
- `--server=file` start lean in server mode, redirecting standard input from the specified file (for debugging)
- `--no-widgets`, `-W` turn off reporting on widgets


Incoming messages to the server are called __requests__ and outgoing messages are called __responses__.
All messages are formatted as JSON objects.
Requests and responses are sent via standard input and standard output.  Each request or response is sent on a separate line.

```ts
interface Request {
    /** command identifier string */
    command : string;
    seq_num? : number;
}

```

`command` is one of a fixed set of command strings shown below, `seq_num` is an optional parameter which lean will use to tag a subsequent response to this request. In this way, multiple requests can be in-flight at the same time.

The response from a command will implement either `CommandResponse` in the case of success, or `ErrorResponse` if an error occurred while handling the request.

```ts
interface CommandResponse extends Response {
    response: 'ok';
    seq_num: number;
}

interface ErrorResponse extends Response {
    response: 'error';
    seq_num?: number;
    message: string;
}
```

# Info

The client may make an `info` request, this is typically triggered by the user moving their cursor to a particular point in the sourcefile.

```ts
interface InfoRequest extends Request {
    command: 'info';
    file_name: string;
    line: number;
    column: number;
}
```

This will cause the lean server to produce the following `InfoResponse`.

```ts
interface InfoResponse extends CommandResponse {
  record?: {
    'full-id'?: string;
    text?: string;
    type?: string;
    doc?: string;
    source?: InfoSource;
    tactic_params?: string[];
    state?: GoalState;
    widget?: WidgetIdentifier;
  }
}
```

In the case that the lean file is still compiling (as indicated by the orange gutter bars in vscode), then instead this will merely return a `{response: "ok"}` response.

# Widgets

Lean attaches __widgets__ to various points in the lean document. These points are added using the `tactic.save_widget` or `tactic.trace_widget` lean constants in the same manner as `tactic.save_info`.
For example, the below Lean code attaches a counter widget to the position occupied by `#html`:

```lean
meta inductive my_action
| increment
| decrement

open my_action

meta def Counter : component unit α :=
component.with_state
     my_action          -- the action of the inner component
     int                -- the state
     (λ _, 0)           -- initialise the state
     (λ _ _ s, s)       -- update the state if the props change
     (λ _ s a,          -- update the state if an action was received
          match a with
          | increment := (s + 1, none) -- replace `none` with `some _` to emit an action
          | decrement := (s - 1, none)
          end
     )
$ component.pure (λ ⟨state, ⟨⟩⟩, [
     button "+" (λ _, increment),
     to_string state,
     button "-" (λ _, decrement)
  ])

#html Counter ()
```

For more information about the API for creating widgets in lean, please consult the [docs in the lean sourcecode](https://github.com/leanprover-community/lean/blob/master/library/init/meta/widget/basic.lean).

In vscode, the user can click on the part of the document marked `#html` and interact with this widget in the info view. In the above example, there is some ephemeral UI state in the form of a counter value. This state is managed in lean and is destroyed when the server quits or if the document is modified above the widget.

## Discovering a widget

In order for a client program to discover and present a widget, the following steps must be performed:

1. Make an `info` request at the position of interest (usually the point under the user's text cursor).
2. Receive an `InfoResponse` object `r`, and extract a `WidgetIdentifier` object `i` from `r.record.widget`. If this is `undefined`, there is no widget at the requested position. Note that `i.column` is the first column containing the widget, not necessarily the column provided by the `info` request.
3. Make a `get_widget` request (see interface below), including the fields of `i`.
4. Recieve a `GetWidgetResponse` object containing the JSON for converting to a DOM object.

```ts
interface WidgetIdentifier {
    line: number;
    column: number;
    id: number;
}

interface GetWidgetRequest extends Request {
    command: 'get_widget';
    file_name: string;
    line: number;
    column: number;
    id: number;
}

interface GetWidgetResponse extends CommandResponse {
    widget: {
        line: number;
        column: number;
        id: number;
        html : WidgetComponent
    };
}

```

### Example: get a widget

```ts
→ {command: "info", file_name: "my_file.lean", line: 25, column: 2, seq_num: 1}
← {response: "ok", seq_num: 1, record: {..., widget: {line: 25, column: 0, id: 51}}}
→ {command: "get_widget", seq_num: 2, file_name: "my_file.lean", line: 25, column: 0, id: 51}
← {response: "ok", seq_num: 2, widget: {line: 25, column: 0, id: 51, html: {...}}}

## Rendering a widget

The recommended UI framework for use with rendering widgets is React, however this is not required.
A reference implementation for React can be found [here](https://github.com/leanprover/vscode-lean/blob/master/infoview/widget.tsx).

After receiving a `GetWidgetResponse` object `r`, the DOM information is stored in `r.widget.html`. This has type `WidgetComponent`, whose schema can be viewed below:


```ts
export interface WidgetEventHandler {
    /** handler id */
    h: number;
    /** route */
    r: number[];
}

export interface WidgetElement {
    /** tag */
    t: string;
    /** children */
    c: WidgetHtml[];
    /** attributes */
    a?: { [k: string]: any };
    /** events */
    e: {
        'onClick'?: WidgetEventHandler;
        'onMouseEnter'?: WidgetEventHandler;
        'onMouseLeave'?: WidgetEventHandler;
    };
    /** tooltip */
    tt?: WidgetHtml;
}

export interface WidgetComponent {
    /** children */
    c: WidgetHtml[];
}

export type WidgetHtml =
    | WidgetComponent
    | string
    | WidgetElement
    | null;
```

### Rendering `WidgetElement`

Ignoring tooltips for now, each `WidgetElement` corresponds to a DOM element.

- `"t"` is the tag of the element.
- `"a"` are the non-event attributes of the element.
- `"e"` are the event handlers that should be attached to the element.
- `"c"` are the children of the element.
- `"tt"` is an additional tooltip element to be discussed below.

For example:

```json
{
  "t": "button",
  "a": {
      "style": {
          "color": "red",
          "padding": "5em",
          "textAlign": "left"
      },
      "className": "b--blue ba",
  },
  "e": {
      "onClick": { "h": 0, "r": [ 51 ] }
  },
  "c": ["hello", "world"]
}
```

Converts to the React element:

```tsx
<button
    style={{color:"red", padding:"5em", textAlign:"left"}}
    className="b--blue ba"
    onClick={() => handle({h:0, r:[51]}, 'onClick')}>
  helloworld
</button>
```


#### Attributes
The attributes field of `WidgetElement` takes the form of a JSON object of keys and values.
Either both the key and value are a string, or a special case is `"style"`, whose value is a JSON object of string key/value pairs.
Events attached to the element are placed in their own `e` field.
Note: the keys of attributes and styles follow the React convention; for example `"textAlign"` and `"onClick"` instead of `"text-align"` and `"on-click"`. Additionally, `"className"` is used instead of `"class"`. So if you are not implementing with React, you will need to convert all of these keynames back to their HTML-native forms.

#### `WidgetElement` Tooltips

Widgets provide special support for 'tooltips' which are pieces of html that appear in 'popovers'. If the `tt` property is set on a `WidgetElement` then the `WidgetHTML` value of `tt` should be rendered in a popover-like element (always, not only when the user hovers their cursor over the element). In the vscode implementation, this is implemented with the popper.js library, where the given WidgetElement is wrapped in an additional `<div/>` also containing the tooltip content. See the [vscode implementation](https://github.com/leanprover/vscode-lean/blob/master/infoview/widget.tsx) for more details.

### Rendering `WidgetComponent`, `null` and `string`

A `WidgetHTML` with value `null` should return an empty html object (in React you can do this by returning `null` or `false`).
If the `WidgetHTML` is a string, then return that string.

A `WidgetComponent` only has one child called `c`. To render a component, simply render all of the child elements and then return them as a list.

#### Examples:
```json
null ↦ null
"hello" ↦ "hello"
{ "c": ["hello", " ", "world"]} ↦ <> hello world </>
```

### Stylesheet

The widgets provided in core lean assume that a CSS stylesheet called `tachyons.css` is loaded. This can be downloaded from tachyons.io. Note that this follows the 'functional CSS' paradigm, so the idea is that the Lean widget-writer should never need to write their own styles, and instead attaches these tachyons classes to their elements.

### Events

There are currently 4 kinds of event handlers that the widget may request:

- `onClick`
- `onMouseEnter`
- `onMouseLeave`
- `onChange` which additionally must supply a string argument to the handler.

In the vscode implementation, `onChange` is only allowed on `input` elements whose `type` attribute is set to `select` or `onChange`.

More information will be provided on events in the next subsection.


### Example

For the above counter code, the `html` object would be:
```json
{ "c": [ {
            "a": null,
            "c": [ {
                    "a": null,
                    "c": [ "+" ],
                    "e": { "onClick": { "h": 0, "r": [ 51 ] } },
                    "t": "button"
                },
                "0",
                {
                    "a": null,
                    "c": [ "-" ],
                    "e": { "onClick": { "h": 1, "r": [ 51 ] } },
                    "t": "button"
                }
            ],
            "t": "div"
        }
    ]
}
```

Which should be converted to the following React DOM:
```jsx
<>
    <button onClick={() => handle({h:0, r:[51]}, 'onClick')}>+</button>
    0
    <button onClick={() => handle({h:1, r:[51]}, 'onClick')}>-<button>
</>
```

## Handling a widget event

When the user interacts with the UI, it may trigger events (eg `onClick` in the above example).
These events must be passed to the Lean server so that the UI can be updated. The procedure for this is as follows:

1. Send an `WidgetEventRequest`:
    ```ts
    interface WidgetEventRequest extends Request {
        command: 'widget_event';
        /** The event kind that caused this request. */
        kind: 'onClick' | 'onMouseEnter' | 'onMouseLeave' | 'onChange';
        /** The handler provided by the `WidgetElement`'s event object. */
        handler: WidgetEventHandler;
        /** use `type:'string'` in the case of `onChange` otherwise use `'unit'` */
        args: { type: 'unit' } | { type: 'string'; value: string };
        file_name: string;
        /** These should be the same as the WidgetIdentifier retrieved from the `get_widget` response. */
        line: number; column: number; id: number;
    }
    ```
2. Receive a `WidgetEventResponse`:
   ```ts
    type WidgetEffect =
        | {kind: 'insert_text'; text: string}
        | {kind: 'reveal_position'; file_name: string; line: number; column: number}
        | {kind: 'highlight_position'; file_name: string; line: number; column: number}
        | {kind: 'clear_highlighting'}
        | {kind: 'copy_text'; text:string}
        | {kind: 'custom'; key: string; value: string}

    interface WidgetEventRecordSuccess {
        status: 'success';
        widget: {
            line: number;
            column: number;
            id: number;
            html : WidgetComponent
        };
        effects?: WidgetEffect[];
    }

    interface WidgetEventRecordInvalid {
        status: 'invalid_handler';
    }

    interface WidgetEventRecordError {
        status: 'error';
        message: string;
    }

    type WidgetEventRecord =
        | WidgetEventRecordSuccess
        | WidgetEventRecordInvalid
        | WidgetEventRecordError;

    interface WidgetEventResponse extends CommandResponse {
        record: WidgetEventRecord;
    }

   ```
   Some branching cases:
   - If the `WidgetEventRecord` has `status: 'error'`, the client should enter an error state and report the error to the user.
   - If the `WidgetEventRecord` has `status: 'invalid'`, then the client should throw away the widget and try getting it again as detailed in the above section.
   - Otherwise, continue to the next step.
3. render the resulting `widget` object in `WidgetEventRecordSuccess` in place of the existing render.
4. If `effects` is not undefined and non-empty, perform these effects in order (details in next section).

### Effects

When a `WidgetEventResponse` is returned, it may contain 'effects' these are changes to the editor state that the UI is requesting.
The list of effects should be applied sequentially in the order they appear in the list.
The currently available effects are:

- `insert_text` should insert the given `text` on the line above the cursor position in the last edited document.
- `reveal_position` should navigate the editor's focus to the given location (file_name, line, column). If the file given by `file_name` is not open, then it should be opened.
- `highlight_position` should add some distinctive text decoration to the given position. If multiple `highlight_position`s are in the effects, this should not cause previous highlights to be removed.
- `clear_highlighting` removes all of the above decoration from all documents.
- `copy_text` should copy the given `text` to the editor's clipboard buffer.
- `custom` is a key-value pair of strings that can be used to add custom editor effects.

### Example: handle a widget event

```ts
↯ users clicks a button
→ {seq_num: 47, command : widget_event, kind:"onClick", handler : {h:0, r: [51]}, file_name: 'my_file.lean', line: 25, column: 0, id: 51, args : { type : "unit", value : {}}}
← {record: {status: "success", widget: {column: 0, html: {...}, id: 51, line: 35}}, response: "ok", seq_num: 47}
```
