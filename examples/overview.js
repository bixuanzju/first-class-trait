class Editor {
    onKey(key) {
        return "Pressing " + key;
    }
    showHelp() {
        // abstract method "version"
        // in Java, we would need abstract version() {...}
        return  "Version: " + this.version() + " Basic usgae...";
    }
    // dynamic dispatch
    doCut() {
        return this.onKey("C-x") + " for cutting texts";
    }
};


// Mixins using first-class class
const modalMixin = Base => {
    return class extends Base {
        constructor() {
            super();
            this.mode = "command";
        }
        version() {
            return 0.1;
        }
        toggleMode() {
            return "toggle succeeded from " + this.mode;
        }
    };
};


// Multiple inheritance using mixins
class ModalEditor extends modalMixin(Editor) {
    // conflicting method
    version() {
        return 0.2;
    }
    // overridden method (using super)
    onKey(key) {
        return super.onKey(key) + " on modal editor";
    }
}

const editor = new Editor();

const editor1 = new ModalEditor();

const editor2 = new ModalEditor();

console.log(editor2.doCut())


// const lineNumMixin = Base => {
//     return class extends Base {
//         // conflicting method
//         version() {
//             return 0.2;
//         }
//         // overridden method (using super)
//         onKey(key) {
//             return super.onKey(key) + " on line editor";
//         }
//     };
// };

// need to resolve conflict here
// const LineModalEditor = lineNumMixin(modalMixin(Editor));