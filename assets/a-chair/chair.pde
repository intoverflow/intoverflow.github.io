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
int ERR_Project_addPart_UNKNOWN_MATERIAL      = - 0x1121;
int ERR_Project_addPart_UNKNOWN_DIM_XWIDTH    = - 0x1122;
int ERR_Project_addPart_UNKNOWN_DIM_YWIDTH    = - 0x1123;

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

  void error_Project_addPart_UNKNOWN_MATERIAL(string in_name, string material) {
    from = "Project_addPart";
    error = ERR_Project_addPart_UNKNOWN_MATERIAL;
    msg = "Unknown material '" + material + "' for part '" + in_name + "'";
  }

  void error_Project_addPart_UNKNOWN_DIM_XWIDTH(string in_name, string dimension) {
    from = "Project_addPart";
    error = ERR_Project_addPart_UNKNOWN_DIM_XWIDTH;
    msg = "Unknown xwidth dimension '" + dimension + "' for part '" + in_name + "'";
  }

  void error_Project_addPart_UNKNOWN_DIM_YWIDTH(string in_name, string dimension) {
    from = "Project_addPart";
    error = ERR_Project_addPart_UNKNOWN_DIM_YWIDTH;
    msg = "Unknown ywidth dimension '" + dimension + "' for part '" + in_name + "'";
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
    the_log.log("info: addPart " + in_name);

    if (!materials.isSet(in_material)) {
      err.error_Project_addPart_UNKNOWN_MATERIAL(in_name, in_material);
      return null;
    }
    if (!dimensions.isSet(in_xwidth)) {
      err.error_Project_addPart_UNKNOWN_DIM_XWIDTH(in_name, in_xwidth);
      return null;
    }
    if (!dimensions.isSet(in_ywidth)) {
      err.error_Project_addPart_UNKNOWN_DIM_YWIDTH(in_name, in_ywidth);
      return null;
    }

    Sheet p = new Sheet(in_name, in_material, in_xwidth, in_ywidth);
    FunHashMap<string, Sheet> new_sheets = sheets.add(err, in_name, p);
    if (err.isFail()) {
      err.propagate("Project_addPart", in_name);
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
    x = m_zoom *m_e2.x + m_center.x;
    y = m_zoom * m_e2.y + m_center.y;
    z = m_zoom * m_e2.z + m_center.z;

    camera(x, y, z, m_center.x, m_center.y, m_center.z, m_e3.x, m_e3.y, m_e3.z);
  }
}


interface WindowView {
  string viewName();
  void mouseDragged();
  void draw();
}

class SheetView implements WindowView {
  Project proj;
  string SHT_sheetname;
  GeneralCamera camera;

  SheetView(Project in_proj, string in_SHT_sheetname) {
    proj = in_proj;
    SHT_sheetname = in_SHT_sheetname;
    camera = new GeneralCamera();
  }

  string viewName() {
    return SHT_sheetname;
  }

  void mouseDragged() {
    if (mouseButton == LEFT) {
      camera.translate(pmouseX - mouseX, mouseY - pmouseY);
    }
    else if (mouseButton == CENTER) {
      camera.tilt(mouseX - pmouseX);
      camera.zoom(pmouseY - mouseY);
    }
  }

  void drawSheet() {
    pushMatrix();
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
      stroke(0, 255, 255);
      fill(0, 255, 255, 255);
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

  void draw() {
    background(50);
    lights();

    hint(DISABLE_DEPTH_TEST);

    textFont(createFont("Courier New"));
    textSize(proj.pcfg.font_size);

    camera.switchTo();
    // ortho(-canvas_width/4, canvas_width/4, -canvas_height/4, canvas_height/4, -1000, 1000);

    /* draw coordinate axis */
    pushMatrix();
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
    popMatrix();

    drawSheet();
  }
}

class ProjectView implements WindowView {
  Project proj;

  HashMap<string, WindowView> windows;
  WindowView current_view;

  ProjectView(Project in_proj, WindowView w) {
    proj = in_proj;
    windows = new HashMap<string, WindowView>();
    addView(w);
    selectView(w.viewName());
  }

  void selectView(string name) {
    current_view = windows.get(name);
    if (null == current_view)
      return;
    ui_set_selected_view(name);
  }

  void addView(WindowView v) {
    windows.put(v.viewName(), v);
    ui_add_view(v.viewName());
  }

  string viewName() {
    return current_view.viewName();
  }

  void mouseDragged() {
    current_view.mouseDragged();
  }

  void draw() {
    /* check to see if the current view is correct */
    if (ui_name_of_selected_view() != viewName())
      selectView(ui_name_of_selected_view());
    current_view.draw();
  }
}




/***********************************************************
 *
 * Driver code
 *
 **********************************************************/

ProjectView proj_view = null;

Project update_if_new(Project old, Project knew) {
  return (null != knew) ? knew : old;
}

void setup () {
  the_log.log("info: starting...");
  ErrorStack err = new ErrorStack();

  /* make the project */
  Project proj = new Project(new ProjectConfig(), "a chair");

  proj = update_if_new(proj, proj.addDimension(err, "0.75in ply thickness", 0.75, UNIT_INCHES) );
  proj = update_if_new(proj, proj.addMaterial(err, "0.75in ply", "0.75in ply thickness") );
  proj = update_if_new(proj, proj.addDimension(err, "0.5in ply thickness", 0.5, UNIT_INCHES) );
  proj = update_if_new(proj, proj.addMaterial(err, "0.5in ply", "0.5in ply thickness") );

  proj = update_if_new(proj, proj.addDimension(err, "sheet 18x12in xwidth", 18, UNIT_INCHES) );
  proj = update_if_new(proj, proj.addDimension(err, "sheet 18x12in ywidth", 12, UNIT_INCHES) );
  proj = update_if_new(proj, proj.addSheet(err, "sheet 18x12x0.75in ply", "0.75in ply", "sheet 18x12in xwidth", "sheet 18x12in ywidth") );

  proj = update_if_new(proj, proj.addDimension(err, "sheet 4x4in xwidth", 4, UNIT_INCHES) );
  proj = update_if_new(proj, proj.addDimension(err, "sheet 4x4in ywidth", 4, UNIT_INCHES) );
  proj = update_if_new(proj, proj.addSheet(err, "sheet 4x4x0.5in ply", "0.5in ply", "sheet 4x4in xwidth", "sheet 4x4in ywidth") );

  if (!err.isFail()) {
    proj_view = new ProjectView(proj, new SheetView(proj, "sheet 18x12x0.75in ply"));
    proj_view.addView(new SheetView(proj, "sheet 4x4x0.5in ply"));

    proj_view.selectView("sheet 4x4x0.5in ply");

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
  proj_view.mouseDragged();
}

void draw() {
  proj_view.draw();
}
