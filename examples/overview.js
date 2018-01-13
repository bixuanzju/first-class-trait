class Editor {
    onKey(key) {
        return "Pressing " + key;
    }
    doCut() {
        return this.onKey("C-x") + " for cutting text";
    }
    showHelp() {
        return  "Version: " + this.version() + " Basic usage...";
    }
};


const spellMixin = Base => {
    return class extends Base {
        check() {
            return super.onKey("C-c") + " for spell checking";
        }
        onKey(key) {
            return "Process " + key + " on spell editor";
        }
    }
};


// Mixins using first-class class
const modalMixin = Base => {
    return class extends Base {
        constructor() {
            super();
            this.mode = "command";
        }
        toggleMode() {
            return "toggle succeeded from " + this.mode;
        }
        onKey(key) {
            return "Process " + key + " on modal editor";
        }
    };
};


// Multiple inheritance using mixins
class ModalEditor extends modalMixin(spellMixin(Editor)) {
   version() {
       return 0.2;
   }
}

const editor = new ModalEditor();

console.log(editor.doCut())