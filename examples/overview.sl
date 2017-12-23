

-- BEGIN_OVERVIEW_EDITOR_TYPES
type Version = { version : String };
type Editor = {
  on_key : String -> String,
  show_help : String,
  do_cut : String
};
-- END_OVERVIEW_EDITOR_TYPES


-- BEGIN_OVERVIEW_EDITOR
trait editor [self : Editor & Version] => {
  on_key(key : String) = "Pressing " ++ key;
  show_help = "Version: " ++ self.version ++ " Basic usage...";
  do_cut = self.on_key "C-x" ++ " for cutting texts"
};
-- END_OVERVIEW_EDITOR



-- BEGIN_OVERVIEW_MODAL
type EditorVer = Editor & Version;
type ModalEdit = { mode : String, toggle_mode : String };

modal_mixin [A * ModalEdit & Version] (base : Trait[EditorVer, Editor & A]) =
  trait [self : ModalEdit & EditorVer] inherits base => {
    mode = "command";
    version = "0.1";
    toggle_mode = "toggle succeeded from " ++ self.mode
  };
-- END_OVERVIEW_MODAL


-- BEGIN_OVERVIEW_LINE
type ModalEditor = ModalEdit & EditorVer;

trait modal_editor [self : ModalEditor] inherits modal_mixin Top editor => {
  -- version = "0.2"
  override on_key(key : String) = super.on_key(key) ++ " on modal editor"
};
-- END_OVERVIEW_LINE

my_editor = new[ModalEditor] modal_editor

main = my_editor.do_cut
