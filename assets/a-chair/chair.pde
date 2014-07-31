canvas_width = 1024;
canvas_height = 576;

/***********************************************************
 *
 * Log class
 * Records events to the app's debug text area
 *
 **********************************************************/

class Log {
  int m_msg_num;

  Log() {
    m_msgnum = 1;
  }

  void log(string s) {
    ui_log(m_msg_num + ": " + s);
    m_msg_num++;
  }
}

Log the_log = new Log();




/***********************************************************
 *
 * Model classes
 *
 **********************************************************/

int ERR_OK        = 0;
int ERR_PROPAGATE = - 0x1000;

int ERR_FunHashMap_add_COLLISION    = - 0x1001;
int ERR_FunHashMap_add_NULL_VALUE   = - 0x1002;
int ERR_FunHashMap_modify_NOTFOUND  = - 0x1003;

int ERR_Project_addMaterial_UNKNOWN_THICKNESS = - 0x1101;
int ERR_Project_addSheet_UNKNOWN_MATERIAL     = - 0x1121;
int ERR_Project_addSheet_UNKNOWN_DIM_XWIDTH   = - 0x1122;
int ERR_Project_addSheet_UNKNOWN_DIM_YWIDTH   = - 0x1123;

int ERR_ProjectController_processCommand_UNKNOWN_CMD_CODE   = - 0x1201;

class ErrorStack {
  int error;
  string from;
  string msg;
  ErrorStack inner_err;

  ErrorStack() {
    from = null;
    error = ERR_OK;
    msg = null;
    inner_err = null;
  }

  void log(Log l) {
    switch (error) {
      case ERR_OK:
        l.log("success");
        break;
      case ERR_PROPAGATE:
        l.log(from + ": propagating while '" + msg + "'");
        inner_err.log(l);
        break;
      default:
        l.log(from + ": error " + error.toString(16) + " " + msg);
        break;
    }
  }

  void propagate(string in_from, string in_msg) {
    ErrorStack new_inner = new ErrorStack();
    new_inner.error = error;
    new_inner.from = from;
    new_inner.msg = msg;
    new_inner.inner_err = inner_err;

    error = ERR_PROPAGATE;
    from = in_from;
    msg = in_msg;
    inner_err = new_inner;
  }

  boolean isFail() {
    return ERR_OK != error;
  }

  void error_FunHashMap_add_COLLISION(string k) {
    from = "FunHashMap_add";
    error = ERR_FunHashMap_add_COLLISION;
    msg = k;
  }

  void error_FunHashMap_add_NULL_VALUE(string k) {
    from = "FunHashMap_add";
    error = ERR_FunHashMap_add_NULL_VALUE;
    msg = k;
  }

  void error_FunHashMap_modify_NOTFOUND(string k) {
    from = "FunHashMap_modify";
    error = ERR_FunHashMap_modify_NOTFOUND;
    msg = k;
  }

  void error_Project_addMaterial_UNKNOWN_THICKNESS(string thickness) {
    from = "Project_addMaterial";
    error = ERR_Project_addMaterial_UNKNOWN_THICKNESS;
    msg = "Unknown thickness dimension '" + thickness + "'";
  }

  void error_Project_addSheet_UNKNOWN_MATERIAL(string in_name, string material) {
    from = "Project_addSheet";
    error = ERR_Project_addSheet_UNKNOWN_MATERIAL;
    msg = "Unknown material '" + material + "' for sheet '" + in_name + "'";
  }

  void error_Project_addSheet_UNKNOWN_DIM_XWIDTH(string in_name, string dimension) {
    from = "Project_addSheet";
    error = ERR_Project_addSheet_UNKNOWN_DIM_XWIDTH;
    msg = "Unknown xwidth dimension '" + dimension + "' for sheet '" + in_name + "'";
  }

  void error_Project_addSheet_UNKNOWN_DIM_YWIDTH(string in_name, string dimension) {
    from = "Project_addSheet";
    error = ERR_Project_addSheet_UNKNOWN_DIM_YWIDTH;
    msg = "Unknown ywidth dimension '" + dimension + "' for sheet '" + in_name + "'";
  }

  void error_ProjectController_processCommand_UNKNOWN_CMD_CODE(int code) {
    from = "ProjectController_processCommand";
    error = ERR_ProjectController_processCommand_UNKNOWN_CMD_CODE;
    msg = "Unknown command code " + code.toString(16);
  }
}

interface EndoFunction<V> {
  static V modify(ErrorStack err, V in);
}

class FunHashMap<K, V> {
  int hash;
  K key;
  V val;
  FunHashMap<K, V> next;

  FunHashMap<K, V>() {
    hash = 0;
    key = null;
    val = null;
    next = null;
  }

  FunHashMap<K, V>(K k, V v, FunHashMap<K, V> tail) {
    hash = k.hashCode();
    key = k;
    val = v;
    next = tail;
  }

  boolean isNil() {
    return (null == val) && (null == next);
  }

  boolean isCons() {
    return (null != val) && (null != next);
  }

  FunHashMap<K, V> add(ErrorStack err, K n_key, V n_val) {
    if (err.isFail())
      return null;

    if (null == n_val) {
      err.error_FunHashMap_add_NULL_VALUE(n_key.toString());
      return null;
    }

    /* make sure the key is not already defined */
    if (isSet(n_key)) {
      err.error_FunHashMap_add_COLLISION(n_key.toString());
      return null;
    }

    /* add it in */
    return new FunHashMap<K, V>(n_key, n_val, this);
  }

  V lookup(K in_key) {
    int in_hash = in_key.hashCode();
    for (FunHashMap<K, V> cur = this; cur != null && cur.isCons(); cur = cur.next) {
      if (in_hash == cur.hash && in_key.equals(cur.key)) {
        return cur.val;
      }
    }

    return null;
  }

  boolean isSet(K in_key) {
    return (null != lookup(in_key));
  }

  FunHashMap<K, V> modify(ErrorStack err, K in_key, EndoFunction<V> in_f) {
    return modify(err, in_key, in_key.hashCode(), in_f);
  }

  FunHashMap<K, V> modify(ErrorStack err, K in_key, int in_hash, EndoFunction<V> in_f) {
    if (err.isFail())
      return null;

    if (isNil()) {
      err.error_FunHashMap_modify_NOTFOUND(in_key.toString());
      return null;
    }

    boolean found = false;

    if (in_hash == hash && in_key.equals(key)) {
      found = true;

      V new_val = in_f.modify(err, val);
      if (err.isFail()) {
        err.propagate("FunHashMap_modify", in_key.toString());
        return null;
      }

      if (null != new_val) {
        return new FunHashMap<K, V>(key, new_val, next);
      }
    }
    else {
      FunHashMap<K, V> new_next = next.modify(err, in_key, in_hash, in_f);
      if (null != new_next)
        return new FunHashMap<K, V>(key, val, new_next);
    }

    return null;
  }
}

class ProjectConfig {
  /* Length in (P3D coordinates) of a 1cm line segment. */
  float fundamental_scale;

  int font_size;

  ProjectConfig() {
    fundamental_scale = 8;
    font_size = 16;
  }
}

int UNIT_UNDEF        = 0x1000;
int UNIT_INCHES       = 0x1001;
int UNIT_CENTIMETERS  = 0x1002;

float DIMENSION_UNDEF_VAL = -1.0;

class Dimension {
  ProjectConfig pcfg;

  string name;
  float val;
  int unit_of_measure;

  Dimension(ProjectConfig in_pcfg, string in_name, float in_val, int in_uom) {
    pcfg = in_pcfg;
    name = in_name;
    val = in_val;
    unit_of_measure = in_uom;
  }

  float P3Dval() {
    float v = val;

    switch (unit_of_measure) {
      case UNIT_INCHES:
        return v * pcfg.fundamental_scale * 2.45;
      case UNIT_CENTIMETERS:
        return v * pcfg.fundamental_scale;
      default:
        the_log.log("Dimension.P3Dval: unknown unit_of_measure '" + unit_of_measure + "'");
    }
  }

  string pretty() {
    float v = val;

    switch (unit_of_measure) {
      case UNIT_UNDEF:
        return v + " [undef]";
      case UNIT_INCHES:
        return v + " in";
      case UNIT_CENTIMETERS:
        return v + " cm";
      default:
        the_log.log("Dimension.pretty: unknown unit_of_measure '" + unit_of_measure + "'");
    }
  }
}

class Material {
  string name;
  string DIM_thickness;

  Material(string in_name, string in_thickness) {
    name = in_name;
    DIM_thickness = in_thickness;
  }
}

class Sheet {
  string name;
  string MAT_material;
  string DIM_xwidth;
  string DIM_ywidth;

  Sheet(string in_name, string in_material, string in_xwidth, string in_ywidth) {
    name = in_name;
    MAT_material = in_material;
    DIM_xwidth = in_xwidth;
    DIM_ywidth = in_ywidth;
  }
}

class Project {
  ProjectConfig pcfg;

  string name;
  FunHashMap<string, Dimension> dimensions;
  FunHashMap<string, Material> materials;
  FunHashMap<string, Sheet> sheets;

  Project(ProjectConfig in_pcfg, string in_name) {
    pcfg = in_pcfg;
    name = in_name;

    dimensions = new FunHashMap<string, Dimension>();
    materials  = new FunHashMap<string, Material>();
    sheets     = new FunHashMap<string, Sheet> ();
  }

  Project(Project copy_from, string in_name
         , FunHashMap<string, Dimension> in_dimensions
         , FunHashMap<string, Material> in_materials
         , FunHashMap<string, Sheet> in_sheets)
  {
    pcfg = copy_from.pcfg;
    name       = (null == in_name)       ? copy_from.name       : in_name;
    dimensions = (null == in_dimensions) ? copy_from.dimensions : in_dimensions;
    materials  = (null == in_materials)  ? copy_from.materials  : in_materials;
    sheets     = (null == in_sheets)     ? copy_from.sheets     : in_sheets;
  }

  Project addDimension(ErrorStack err, string in_name, float in_val, int in_uom) {
    if (err.isFail())
      return null;
    the_log.log("info: addDimension " + in_name);

    Dimension d = new Dimension(pcfg, in_name, in_val, in_uom);
    FunHashMap<string, Dimension> new_dimensions = dimensions.add(err, in_name, d);
    if (err.isFail()) {
      err.propagate("Project_addDimension", in_name);
      return null;
    }

    Project np = (null == new_dimensions) ? null : new Project(this, null, new_dimensions, null, null);
    return np;
  }

  Project addMaterial(ErrorStack err, string in_name, string in_thickness) {
    if (err.isFail())
      return null;
    the_log.log("info: addMaterial " + in_name);

    if (!dimensions.isSet(in_thickness)) {
      err.error_Project_addMaterial_UNKNOWN_THICKNESS(in_name, in_thickness);
      return null;
    }

    Material m = new Material(in_name, in_thickness);
    FunHashMap<string, Material> new_materials = materials.add(err, in_name, m);
    if (err.isFail()) {
      err.propagate("Project_addMaterial", in_name);
      return null;
    }

    Project np = (null == new_materials) ? null : new Project(this, null, null, new_materials, null);
    return np;
  }

  Project addSheet(ErrorStack err, string in_name, string in_material, string in_xwidth, string in_ywidth) {
    if (err.isFail())
      return null;
    the_log.log("info: addSheet " + in_name);

    if (!materials.isSet(in_material)) {
      err.error_Project_addSheet_UNKNOWN_MATERIAL(in_name, in_material);
      return null;
    }
    if (!dimensions.isSet(in_xwidth)) {
      err.error_Project_addSheet_UNKNOWN_DIM_XWIDTH(in_name, in_xwidth);
      return null;
    }
    if (!dimensions.isSet(in_ywidth)) {
      err.error_Project_addSheet_UNKNOWN_DIM_YWIDTH(in_name, in_ywidth);
      return null;
    }

    Sheet p = new Sheet(in_name, in_material, in_xwidth, in_ywidth);
    FunHashMap<string, Sheet> new_sheets = sheets.add(err, in_name, p);
    if (err.isFail()) {
      err.propagate("Project_addSheet", in_name);
      return null;
    }

    Project np = (null == new_sheets) ? null : new Project(this, null, null, null, new_sheets);
    return np;
  }
}



/***********************************************************
 *
 * View classes
 *
 **********************************************************/

class Vec3D {
  /* remember: left-handed coordinate frame! */
  float x;
  float y;
  float z;

  Vec3D(float in_x, float in_y, float in_z) {
    x = in_x;
    y = in_y;
    z = in_z;
  }

  Vec3D rotateAboutPure(Vec3D u, float angle) {
    float c = cos(angle);
    float s = sin(angle);

    float a11 = c + u.x*u.x*(1-c);
    float a12 = u.x*u.y*(1-c) - u.z*s;
    float a13 = u.x*u.z*(1-c) + u.y*s;

    float a21 = u.y*u.x*(1-c) + u.z*s;
    float a22 = c + u.y*u.y*(1-c);
    float a23 = u.y*u.z*(1-c) - u.x*s;

    float a31 = u.z*u.x*(1-c) - u.y*s;
    float a32 = u.z*u.y*(1-c) + u.x*s;
    float a33 = c + u.z*u.z*(1-c);

    return new Vec3D(a11 * x + a12 * y + a13 * z
                    ,a21 * x + a22 * y + a23 * z
                    ,a31 * x + a32 * y + a33 * z);
  }

  void rotateAbout(Vec3D u, float angle) {
    Vec3D n = rotateAboutPure(u, angle);
    x = n.x;
    y = n.y;
    z = n.z;
  }

  float dotPute(Vec3D v) {
    return x*v.x + y*v.y + z*v.z;
  }

  float normPure() {
    return sqrt(x*x + y*y + z*z);
  }

  void scale(float s) {
    x *= s;
    y *= s;
    z *= s;
  }

  void normalize() {
    float n = normPure();
    if (n > 0)
      scale(n);
  }
}

class GeneralCamera {
  /* remember: left-handed coordinate frame! */
  Vec3D m_e1; /* right ("x") */
  Vec3D m_e2; /* zoom ("y") */
  Vec3D m_e3; /* up ("z") */
  float m_zoom;
  float m_zoom_speed;

  float m_tilt;
  float m_tilt_speed;

  Vec3D m_center;
  float m_translate_speed;

  GeneralCamera() {
    m_zoom_speed = 1;
    m_tilt_speed = PI / 6 * 0.01;
    m_translate_speed = PI / 6 * 0.01;

    gotoDefault();
  }

  void gotoDefault() {
    m_e1 = new Vec3D(1, 0, 0); /* right ("x") */
    m_e2 = new Vec3D(0, 1, 0); /* zoom ("y") */
    m_e3 = new Vec3D(0, 0, -1); /* up ("z") */
    m_zoom = 600;

    m_tilt = 0;

    m_center = new Vec3D(0, 0, 0);

    translate(70, 180);
  }

  void translate(float dX, float dZ) {
    if (0 == dX || 0 == dZ) {
      Vec3D axis;
      if (0 == dX && 0 != dZ) {
        axis = new Vec3D(m_e1.x, m_e1.y, m_e1.z);
        if (dZ < 0) axis.scale(-1);
      }
      else if (0 != dX && 0 == dZ) {
        axis = new Vec3D(m_e3.x, m_e3.y, m_e3.z);
        if (dX < 0) axis.scale(-1);
      }

      if (0 != dX || 0 != dZ) {
        float angle = sqrt(dX*dX + dZ*dZ) * m_translate_speed;
        m_e1.rotateAbout(axis, angle);
        m_e2.rotateAbout(axis, angle);
        m_e3.rotateAbout(axis, angle);
      }
    }
    else {
      float angle_of_rotation = atan(dZ/dX);

      Vec3D axis = m_e3.rotateAboutPure(m_e2, -angle_of_rotation);

      float angle = sqrt(dX*dX + dZ*dZ) * m_translate_speed;
      if (dX < 0)
        angle *= -1;
      m_e1.rotateAbout(axis, angle);
      m_e2.rotateAbout(axis, angle);
      m_e3.rotateAbout(axis, angle);
    }
  }

  void tilt(float dY) {
    m_e1.rotateAbout(m_e2, dY * m_tilt_speed);
    m_e3.rotateAbout(m_e2, dY * m_tilt_speed);
  }

  void zoom(float steps) {
    float zoom_velocity = - steps * m_zoom_speed;

    m_zoom += zoom_velocity;
    if (m_zoom < 75)
      m_zoom = 75;
  }

  void switchTo() {
    x = m_zoom * m_e2.x + m_center.x;
    y = m_zoom * m_e2.y + m_center.y;
    z = m_zoom * m_e2.z + m_center.z;

    camera(x, y, z, m_center.x, m_center.y, m_center.z, m_e3.x, m_e3.y, m_e3.z);
  }
}



class Color {
  int r;
  int g;
  int b;

  Color(int color) {
    r = (color & 0x00ff0000) >> 16;
    g = (color & 0x0000ff00) >> 8;
    b = color & 0x000000ff;
  }
}

interface HUDElement {
  float xwidth();
  float ywidth();
  void draw(float x, float y);
}

class HUDButton implements HUDElement {
  Color cstroke;
  Color cfill;
  Color clabel;
  float m_xwidth;
  float m_ywidth;
  string label;

  HUDButton(Color in_cstroke, Color in_cfill, Color in_clabel, float in_xwidth, float in_ywidth, string in_label) {
    cstroke = in_cstroke;
    cfill = in_cfill;
    clabel = in_clabel;
    m_xwidth = in_xwidth;
    m_ywidth = in_ywidth;
    label = in_label;
  }

  float xwidth() { return m_xwidth; }
  float ywidth() { return m_ywidth; }

  void draw(float x, float y) {
    strokeWeight(2);
    stroke(cstroke.r, cstroke.g, cstroke.b);
    fill(cfill.r, cfill.g, cfill.b);
    rect(x, y, m_xwidth, m_ywidth);
    fill(clabel.r, clabel.g, clabel.b);
    text(label, x, y + textAscent());
  }
}

class HUDVertical implements HUDElement {
  ArrayList<HUDElement> elements;

  HUDVertical() {
    elements = new ArrayList<HUDElement>();
  }

  void addTop(HUDElement n) {
    elements.add(0, n);
  }

  void addBottom(HUDElement n) {
    elements.add(n);
  }

  float spacing() { return 5; }

  float xwidth() {
    float x = 0;
    for (int i = 0; i < elements.size(); i++) {
      float nx = elements.get(i).xwidth();
      x = (x < nx) ? nx : x;
    }
    return x;
  }

  float ywidth() {
    float y = 0;
    for (int i = 0; i < elements.size(); i++) {
      y += elements.get(i).ywidth() + (0 < i ? spacing() : 0);
    }
    return y;
  }

  void draw(float x, float y) {
    for (int i = 0; i < elements.size(); i++) {
      elements.get(i).draw(x, y);
      y += elements.get(i).ywidth() + spacing();
    }
  }
}

class HUDHorizontal implements HUDElement {
  ArrayList<HUDElement> elements;

  HUDHorizontal() {
    elements = new ArrayList<HUDElement>();
  }

  void addLeft(HUDElement n) {
    elements.add(0, n);
  }

  void addRight(HUDElement n) {
    elements.add(n);
  }

  float spacing() { return 5; }

  float xwidth() {
    float x = 0;
    for (int i = 0; i < elements.size(); i++) {
      x += elements.get(i).xwidth() + (0 < i ? spacing() : 0);
    }
    return x;
  }

  float ywidth() {
    float y = 0;
    for (int i = 0; i < elements.size(); i++) {
      float ny = elements.get(i).ywidth();
      y = (y < ny) ? ny : y;
    }
    return y;
  }

  void draw(float x, float y) {
    for (int i = 0; i < elements.size(); i++) {
      elements.get(i).draw(x, y);
      x += elements.get(i).xwidth() + spacing();
    }
  }
}



interface WindowView {
  string viewName();
  void mouseDragged();
  void draw(Project proj);
}

class SheetView implements WindowView {
  string SHT_sheetname;
  GeneralCamera cam;

  SheetView(string in_SHT_sheetname) {
    SHT_sheetname = in_SHT_sheetname;
    cam = new GeneralCamera();
  }

  string viewName() {
    return SHT_sheetname;
  }

  void mouseDragged() {
    if (mouseButton == LEFT) {
      cam.translate(pmouseX - mouseX, mouseY - pmouseY);
    }
    else if (mouseButton == CENTER) {
      cam.tilt(mouseX - pmouseX);
      cam.zoom(pmouseY - mouseY);
    }
  }

  void drawSheet(Project proj) {
    pushMatrix();
      strokeWeight(1.5);
      stroke(255);
      fill(127, 127, 127, 127);

      translate(0, 0, 0);

      /* fetch sheet */
      Sheet sheet = proj.sheets.lookup(SHT_sheetname);
      Dimension xwidth = proj.dimensions.lookup(sheet.DIM_xwidth);
      Dimension ywidth = proj.dimensions.lookup(sheet.DIM_ywidth);
      Material mat = proj.materials.lookup(sheet.MAT_material);
      Dimension zwidth = proj.dimensions.lookup(mat.DIM_thickness);
      float x = xwidth.P3Dval();
      float y = ywidth.P3Dval();
      float z = zwidth.P3Dval();

      /* draw the sheet */
      box(x, y, z);

      /* draw the widths */
      strokeWeight(1);
      stroke(0, 255, 255);
      fill(0, 255, 255, 255);
      textMode(SHAPE)
      textSize(proj.pcfg.font_size);
      line( x/2 + 5, -(y/2), -z/2
          , x/2 + 5,   y/2 , -z/2
          );
      text(xwidth.pretty(), 0, y/2+10, -z/2);
      line( -(x/2), y/2 + 5, -z/2
          ,   x/2 , y/2 + 5, -z/2
          );
      text(ywidth.pretty(), x/2+10, 0, -z/2);
    popMatrix();
  }

  void draw(Project proj) {
    textFont(createFont("Courier New"));

    background(50);

    /* draw model */
    {
      cam.switchTo();
      hint(DISABLE_DEPTH_TEST);
      lights();

      drawCoordinateAxis(proj);
      drawSheet(proj);
    }

    /* draw HUD */
    {
      camera();
      hint(DISABLE_DEPTH_TEST);

      noLights();
      drawHUD(proj);
    }
  }

  void drawCoordinateAxis(Project proj) {
    strokeWeight(1);

    stroke(255, 0, 0);
    line(0, 0, 0, 1000, 0, 0);
    stroke(127, 0, 0);
    line(0, 0, 0, -1000, 0, 0);

    stroke(0, 255, 0);
    line(0, 0, 0, 0, 1000, 0);
    stroke(0, 127, 0);
    line(0, 0, 0, 0, -1000, 0);


    stroke(0, 0, 255);
    line(0, 0, 0, 0, 0, 1000);
    stroke(0, 0, 127);
    line(0, 0, 0, 0, 0, -1000);
  }

  void drawHUD(Project proj) {
    textMode(MODEL);
    textSize(10);

    /* view name */
    fill(255);
    text(viewName(), 10, canvas_height - (10 + textAscent()));

    /* hud */
    Color btn_stroke = new Color(0x00a1a1a1);
    Color btn_fill = new Color(0x00464646);
    Color btn_label = new Color(0x00ffffff);

    HUDVertical hud1 = new HUDVertical();
    hud1.addBottom(new HUDButton(btn_stroke, btn_fill, btn_label, 80, 20, "toggle hud"));
    hud1.addBottom(new HUDButton(btn_stroke, btn_fill, btn_label, 80, 20, "add sheet"));
    hud1.addBottom(new HUDButton(btn_stroke, btn_fill, btn_label, 80, 20, "add part"));


    HUDVertical hud2 = new HUDVertical();
    hud2.addBottom(new HUDButton(btn_stroke, btn_fill, btn_label, 50, 20, "eat"));
    hud2.addBottom(new HUDButton(btn_stroke, btn_fill, btn_label, 60, 20, "sleep"));

    HUDVertical hud3 = new HUDVertical();
    hud3.addBottom(new HUDButton(btn_stroke, btn_fill, btn_label, 90, 20, "rave"));
    hud3.addBottom(new HUDButton(btn_stroke, btn_fill, btn_label, 90, 45, "repeat"));

    HUDHorizontal hud_a = new HUDHorizontal();
    hud_a.addRight(hud1);
    hud_a.addRight(hud2);
    hud_a.addRight(hud3);

    HUDVertical hud = new HUDVertical();
    hud.addBottom(hud_a);
    hud.addBottom(new HUDButton(btn_stroke, btn_fill, btn_label, 240, 30, "execute command"));

    hud.draw(10, 10);
  }
}


class ProjectView implements WindowView {
  FunHashMap<string, WindowView> windows;
  WindowView current_view;

  int ref_count;

  ProjectView() {
    windows = new FunHashMap<string, WindowView>();
    current_view = null;
    ref_count = 0;
  }

  ProjectView(FunHashMap<string, WindowView> in_windows) {
    windows = in_windows;
    current_view = null;
    ref_count = 0;
  }

  void selectView(string name) {
    current_view = windows.lookup(name);
  }

  ProjectView addView(ErrorStack err, WindowView v) {
    if (err.isFail())
      return null;

    FunHashMap<string, WindowView> new_windows = windows.add(err, v.viewName(), v);
    if (err.isFail()) {
      err.propagate("ProjectView_addView", "adding view '" + v.viewName() + "'");
      return null;
    }

    if (ref_count <= 1) {
      windows = new_windows;
      return null;
    }

    ProjectView n = new ProjectView(new_windows);
    if (null != current_view)
      n.selectView(viewName());

    return n;
  }

  string viewName() {
    return (null != current_view) ? current_view.viewName() : "[master view]";
  }

  void mouseDragged() {
    if (null != current_view)
      current_view.mouseDragged();
  }

  void draw(Project proj) {
    if (null != current_view)
      current_view.draw(proj);
  }
}




/***********************************************************
 *
 * Controller classes
 *
 **********************************************************/

class ProjectTree {
  Project proj;
  ProjectView view;
  ProjectTree parent;
  ArrayList<ProjectTree> children;

  ProjectTree(Project in_proj, ProjectView in_view) {
    proj = in_proj;
    view = in_view;
    parent = null;
    children = new ArrayList<ProjectTree>();

    view.ref_count++;
  }

  ProjectTree addChild(Project in_child, ProjectView in_view) {
    ProjectTree child = new ProjectTree(in_child, in_view);
    child.parent = this;

    children.add(child);
    return child;
  }
}

interface Command {
  int commandCode();
  string pretty();
}

int CMD_CODE_ADD_DIMENSION  = 0x1001;
int CMD_CODE_ADD_MATERIAL   = 0x1002;
int CMD_CODE_ADD_SHEET      = 0x1003;

int CMD_CODE_VIEW_SELECT    = 0x1103;

class CmdAddDimension implements Command {
  string name;
  float val;
  int unit_of_measure;

  CmdAddDimension(string in_name, float in_val, int in_unit_of_measure) {
    name = in_name;
    val = in_val;
    unit_of_measure = in_unit_of_measure;
  }

  int commandCode() { return CMD_CODE_ADD_DIMENSION; }

  string pretty() {
    return "dimension add: '" + name + "' '" + val + "' '" + unit_of_measure + "'";
  }
}

class CmdAddMaterial implements Command {
  string name;
  string thickness;

  CmdAddMaterial(string in_name, string in_thickness) {
    name = in_name;
    thickness = in_thickness;
  }

  int commandCode() { return CMD_CODE_ADD_MATERIAL; }

  string pretty() {
    return "material add: '" + name + "' '" + thickness + "'";
  }
}

class CmdAddSheet implements Command {
  string name;
  string material;
  string xwidth;
  string ywidth;

  CmdAddSheet(string in_name, string in_material, string in_xwidth, string in_ywidth) {
    name = in_name;
    material = in_material;
    xwidth = in_xwidth;
    ywidth = in_ywidth;
  }

  int commandCode() { return CMD_CODE_ADD_SHEET; }

  string pretty() {
    return "sheet add: '" + name + "' '" + material + "' '" + xwidth + "' '" + ywidth + "'";
  }
}

class CmdViewSelect implements Command {
  string view_name;

  CmdViewSelect(string in_view_name) {
    view_name = in_view_name;
  }

  int commandCode() { return CMD_CODE_VIEW_SELECT; }

  string pretty() {
    return "view select: '" + view_name + "'";
  }
}

class ProjectController {
  ProjectTree project_tree;

  ProjectController(Project in_proj, ProjectView in_view) {
    project_tree = new ProjectTree(in_proj, in_view);
  }

  Project project() {
    return project_tree.proj;
  }

  ProjectView view() {
    return project_tree.view;
  }

  void processCommand(ErrorStack err, Command cmd) {
    if (err.isFail())
      return;

    Project np = null;
    ProjectView nv = null;

    switch (cmd.commandCode()) {
      case CMD_CODE_ADD_DIMENSION:
        {
          CmdAddDimension ccmd = (CmdAddDimension)cmd;
          np = project().addDimension(err, ccmd.name, ccmd.val, ccmd.unit_of_measure);
          if (err.isFail()) {
            err.propagate("ProjectController_processCommand", "adding dimension '" + ccmd.name + "'");
            return;
          }
        }
        break;
      case CMD_CODE_ADD_MATERIAL:
        {
          CmdAddMaterial ccmd = (CmdAddMaterial)cmd;
          np = project().addMaterial(err, ccmd.name, ccmd.thickness);
          if (err.isFail()) {
            err.propagate("ProjectController_processCommand", "adding material '" + ccmd.name + "'");
            return;
          }
        }
        break;
      case CMD_CODE_ADD_SHEET:
        {
          CmdAddSheet ccmd = (CmdAddSheet)cmd;
          np = project().addSheet(err, ccmd.name, ccmd.material, ccmd.xwidth, ccmd.ywidth);
          if (err.isFail()) {
            err.propagate("ProjectController_processCommand", "adding sheet '" + ccmd.name + "'");
            return;
          }
          nv = view().addView(err, new SheetView(ccmd.name));
          if (err.isFail()) {
            err.propagate("ProjectController_processCommand", "adding view '" + ccmd.name + "'");
            return;
          }
          project_tree.view.selectView(ccmd.name);
        }
        break;
      case CMD_CODE_VIEW_SELECT:
        {
          CmdViewSelect ccmd = (CmdViewSelect)cmd;
          nv = view().selectView(ccmd.view_name);
        }
        break;
      default:
        err.error_ProjectController_processCommand_UNKNOWN_CMD_CODE(cmd.commandCode());
        return;
    }

    the_log.log("info: processed command '" + cmd.pretty() + "'");

    if (null != np || null != nv)
      project_tree = project_tree.addChild((null == np) ? project() : np, (null == nv) ? view() : nv);
  }
}



/***********************************************************
 *
 * Driver code
 *
 **********************************************************/

ProjectController proj_controller = null;

void setup () {
  the_log.log("info: starting...");
  ErrorStack err = new ErrorStack();

  /* make the project */
  proj_controller = new ProjectController(new Project(new ProjectConfig(), "a chair"), new ProjectView());


  proj_controller.processCommand(err, new CmdAddDimension("0.75in ply thickness", 0.75, UNIT_INCHES));
  proj_controller.processCommand(err, new CmdAddMaterial("0.75in ply", "0.75in ply thickness"));

  proj_controller.processCommand(err, new CmdAddDimension("0.5in ply thickness", 0.5, UNIT_INCHES));
  proj_controller.processCommand(err, new CmdAddMaterial("0.5in ply", "0.5in ply thickness"));

  proj_controller.processCommand(err, new CmdAddDimension("sheet 18x12in xwidth", 18, UNIT_INCHES));
  proj_controller.processCommand(err, new CmdAddDimension("sheet 18x12in ywidth", 12, UNIT_INCHES));
  proj_controller.processCommand(err, new CmdAddSheet("sheet 18x12x0.75in ply", "0.75in ply", "sheet 18x12in xwidth", "sheet 18x12in ywidth"));

  proj_controller.processCommand(err, new CmdAddDimension("sheet 4x4in width", 4, UNIT_INCHES));
  proj_controller.processCommand(err, new CmdAddSheet("sheet 4x4x0.5in ply", "0.5in ply", "sheet 4x4in width", "sheet 4x4in width"));

  proj_controller.processCommand(err, new CmdViewSelect("sheet 18x12x0.75in ply"));


  if (!err.isFail()) {
    size(canvas_width, canvas_height, P3D);
    frameRate(120);

    the_log.log("info: started");
  }
  else {
    the_log.log("ERROR: setup aborted");
    err.propagate("setup", "initializing project");
    err.log(the_log);
  }

  return;
}

void mouseDragged() {
  proj_controller.view().mouseDragged();
}

void draw() {
  proj_controller.view().draw(proj_controller.project());
}
