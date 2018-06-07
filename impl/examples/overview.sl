--> "Pressing C-x on modal editor 0.2 based on version 0.1 for cutting texts"

type Editor = { version : String, on_key : String -> String, do_cut : String };

trait editor [self : Editor] => {
  version = "0.1";
  on_key(key : String) = "Pressing " ++ key;
  do_cut = self.on_key "C-x" ++ " for cutting texts"
};

-- First-class traits and dynamic inheritance and abstract method
type ShowHelp = { show_help : String };

help_mixin [A * ShowHelp] (base : Trait[Editor, Editor & A]) =
  trait [self : Editor] inherits base => {
    show_help = "Version: " ++ self.version ++ " Basic usage..."
  };

type ModalEdit = { mode : String, toggle_mode : String};

modal_mixin [A * ModalEdit] (base : Trait[Editor, Editor & A]) =
  trait [self : Editor & ModalEdit] inherits base => {
    mode = "command";
    -- version = "0.2";
    toggle_mode = "toggle succeeded from " ++ self.mode
  };


type ModalEditor = Editor & ModalEdit & ShowHelp;

trait modal_editor [self : ModalEditor]
  inherits modal_mixin ShowHelp (help_mixin Top editor) => {
    override on_key(key : String) = super.on_key(key) ++ " on modal editor"
};

a_editor1 = new[Editor] editor;

type Version = { version : String };

trait help [self : Version] => {
  show_help = "Version: " ++ self.version ++ " Basic usage..."
};


trait editor2 [self : Editor] inherits editor & help => {};


modal (init_mode : String) = trait [self : ModalEdit] => {
  mode = init_mode;
  version = "0.2";
  toggle_mode = "toggle succeeded from " ++ self.mode
};

{-
modal_editor (init_mode : String) = trait [self : ModalEditor]
  -- conflict
  inherits editor & help & modal init_mode => {
    override on_key(key : String) = super.on_key(key) ++ " on modal editor"
};
-}

modal_editor (init_mode : String) = trait [self : ModalEditor]
  inherits editor \ { version : String } & help & modal init_mode => {
    override on_key(key : String) = super.on_key(key) ++ " on modal editor"
};

modal_editor2 (init_mode : String) = trait [self : ModalEditor]
  inherits editor \ { version : String } & help & modal init_mode => {
    override on_key(key : String) = super.on_key(key)
      ++ " on modal editor "
      ++ self.version ++ " based on version " ++ (editor ^ self).version
};


-- BEGIN_MERGE
merge A [B * A] (x : Trait[A]) (y : Trait[B]) = new[A & B] x & y;
-- END_MERGE

a_editor2 = new[ModalEditor] modal_editor2 "command";
main = a_editor2.do_cut
-- Output:
-- "Pressing C-x on modal editor 0.2 based on version 0.1 for cutting texts"
