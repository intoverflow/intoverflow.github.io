canvas_width = 1024;
canvas_height = 576;



/***********************************************************
 *
 * Model classes
 *
 **********************************************************/

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
        return v + " [" + unit_of_measure + "]";
    }
  }
}

class Material {
  ProjectConfig pcfg;

  string name;
  string DIM_thickness;

  Material(ProjectConfig in_pcfg, string in_name, string in_thickness) {
    pcfg = in_pcfg;
    name = in_name;
    DIM_thickness = in_thickness;
  }
}

class Part {
  ProjectConfig pcfg;

  string name;
  string MAT_material;
  string DIM_xwidth;
  string DIM_ywidth;

  Part(ProjectConfig in_pcfg, string in_name, string in_material, string in_xwidth, string in_ywidth) {
    pcfg = in_pcfg;
    name = in_name;
    MAT_material = in_material;
    DIM_xwidth = in_xwidth;
    DIM_ywidth = in_ywidth;
  }
}

class Project {
  ProjectConfig pcfg;

  string name;
  HashMap<string, Dimension> dimensions;
  HashMap<string, Material> materials;
  HashMap<string, Part> parts;

  Project(ProjectConfig in_pcfg, string in_name) {
    pcfg = in_pcfg;
    name = in_name;

    dimensions = new HashMap<string, Dimension>();
    materials  = new HashMap<string, Material>();
    parts      = new HashMap<string, Part> ();
  }

  boolean addDimension(string in_name, float in_val, int in_uom) {
    if (dimensions.containsKey(in_name))
      return false;
    Dimension d = new Dimension(pcfg, in_name, in_val, in_uom);
    dimensions.put(in_name, d);
    return true;
  }

  boolean addMaterial(string in_name, string in_thickness) {
    if (!dimensions.containsKey(in_thickness))
      return false;
    if (materials.containsKey(in_name))
      return false;
    Material m = new Material(pcfg, in_name, in_thickness);
    materials.put(in_name, m);
    return true;
  }

  boolean addPart(string in_name, string in_material, string in_xwidth, string in_ywidth) {
    if (!materials.containsKey(in_material))
      return false;
    if (!dimensions.containsKey(in_xwidth))
      return false;
    if (!dimensions.containsKey(in_ywidth))
      return false;
    if (parts.containsKey(in_name))
      return false;
    Part p = new Part(pcfg, in_name, in_material, in_xwidth, in_ywidth);
    parts.put(in_name, p);
    return true;
  }
}



void drawPart(Project proj, string pname) {
  pushMatrix();
    stroke(255);
    fill(127, 127, 127, 127);

    translate(0, 0, 0);

    /* fetch part */
    Part part = proj.parts.get(pname);
    if (null == part) goto drawPart_abort;

    Dimension xwidth = proj.dimensions.get(part.DIM_xwidth);
    Dimension ywidth = proj.dimensions.get(part.DIM_ywidth);
    if (null == xwidth || null == ywidth) goto drawPart_abort;

    Material mat = proj.materials.get(part.MAT_material);
    if (null == mat) goto drawPart_abort;

    Dimension zwidth = proj.dimensions.get(mat.DIM_thickness);
    if (null == zwidth) goto drawPart_abort;

    float x = xwidth.P3Dval();
    float y = ywidth.P3Dval();
    float z = zwidth.P3Dval();

    /* draw the part */
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

drawPart_abort:
  popMatrix();
}



/***********************************************************
 *
 * Log class
 * Records events to the app's debug text area
 *
 **********************************************************/

class Log {
  var m_textarea;
  int m_msg_num;

  Log() {
    m_textarea = document.getElementById("app-log");
    m_msgnum = 1;
  }

  void log(string s) {
    m_textarea.value = (m_msg_num + ": " + s + "\n" + m_textarea.value);
    m_msg_num++;
  }
}



/***********************************************************
 *
 * Vector class
 * Some simple vector operations supported
 *
 **********************************************************/

class Vec3D {
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



/***********************************************************
 *
 * Camera class
 * The window into the model
 *
 **********************************************************/

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
  }

  void gotoDefault() {
    m_e1 = new Vec3D(1, 0, 0); /* right ("x") */
    m_e2 = new Vec3D(0, 1, 0); /* zoom ("y") */
    m_e3 = new Vec3D(0, 0, -1); /* up ("z") */
    m_zoom = 500;

    m_tilt = 0;

    m_center = new Vec3D(0, 0, 0);
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

        the_log.log("translate by (" + dX + ", " + dZ + ") " + angle);
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

      the_log.log("translate by (" + dX + ", " + dZ + ") " + angle_of_rotation + " " + angle);
    }
  }

  void tilt(float dY) {
    m_e1.rotateAbout(m_e2, dY * m_tilt_speed);
    m_e3.rotateAbout(m_e2, dY * m_tilt_speed);

    the_log.log("tilt by " + dY);
  }

  void zoom(float steps) {
    float zoom_velocity = - steps * m_zoom_speed;

    m_zoom += zoom_velocity;
    if (m_zoom < 75)
      m_zoom = 75;

    the_log.log("zoom by " + zoom_velocity);
  }

  void switchTo() {
    x = m_zoom *m_e2.x + m_center.x;
    y = m_zoom * m_e2.y + m_center.y;
    z = m_zoom * m_e2.z + m_center.z;

    camera(x, y, z, m_center.x, m_center.y, m_center.z, m_e3.x, m_e3.y, m_e3.z);
  }
}



/***********************************************************
 *
 * Driver code
 *
 **********************************************************/

Log the_log = new Log();

GeneralCamera cam = new GeneralCamera();

void draw() {
  noStroke();
  background(50);
  lights();

  hint(DISABLE_DEPTH_TEST);

  Project proj = new Project(new ProjectConfig(), "a chair");

  textFont(createFont("Courier New"));
  textSize(proj.pcfg.font_size);

  if (!proj.addDimension("0.75in ply thickness", 0.75, UNIT_INCHES)) goto draw_abort;
  if (!proj.addMaterial("0.75in ply", "0.75in ply thickness")) goto draw_abort;
  if (!proj.addDimension("p1 xwidth", 18, UNIT_INCHES)) goto draw_abort;
  if (!proj.addDimension("p1 ywidth", 3.5, UNIT_INCHES)) goto draw_abort;
  if (!proj.addPart("part1", "0.75in ply", "p1 xwidth", "p1 ywidth")) goto draw_abort;

  cam.switchTo();
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

  /* draw part */
  drawPart(proj, "part1");

draw_abort:
  return;
}

void setup () {
  size(canvas_width, canvas_height, P3D);
  frameRate(120);
  cam.gotoDefault();
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
