canvas_width = 1024;
canvas_height = 576;

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
 * Camera class
 * Records events to the app's debug text area
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

  void rotateAbout(Vec3D u, float angle) {
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

    nx = a11 * x + a12 * y + a13 * z;
    ny = a21 * x + a22 * y + a23 * z;
    nz = a31 * x + a32 * y + a33 * z;

    x = nx; y = ny; z = nz;
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
  }

  void gotoDefault() {
    m_e1 = new Vec3D(1, 0, 0); /* right ("x") */
    m_e2 = new Vec3D(0, 1, 0); /* zoom ("y") */
    m_e3 = new Vec3D(0, 0, -1); /* up ("z") */
    m_zoom = 400;

    m_tilt = 0;

    m_center = new Vec3D(0, 0, 0);
  }

  void translate(float dX, float dY) {
    m_e1.rotateAbout(m_e3, dX * m_translate_speed);
    m_e1.rotateAbout(m_e3, dX * m_translate_speed);

    m_e2.rotateAbout(m_e3, dX * m_translate_speed);
    m_e2.rotateAbout(m_e3, dX * m_translate_speed);


    m_e2.rotateAbout(m_e1, dY * m_translate_speed);
    m_e2.rotateAbout(m_e1, dY * m_translate_speed);

    m_e3.rotateAbout(m_e3, dY * m_translate_speed);
    m_e3.rotateAbout(m_e3, dY * m_translate_speed);

    the_log.log("translate by (" + dX + ", " + dY + ")");
  }

  void tilt(float d) {
    m_e1.rotateAbout(m_e2, d * m_tilt_speed);
    m_e1.rotateAbout(m_e2, d * m_tilt_speed);

    m_e3.rotateAbout(m_e2, d * m_tilt_speed);
    m_e3.rotateAbout(m_e2, d * m_tilt_speed);

    the_log.log("tilt by " + d);
  }

  void zoom(float steps) {
    float zoom_velocity = - steps * m_zoom_speed;

    m_zoom += zoom_velocity;

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

  cam.switchTo();

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

  stroke(255);

  pushMatrix();
    rotateZ(PI/3);

    translate(30, 0, 0);
    rotateX(-PI/6);
    rotateY(PI/3 + 210/float(height) * PI);
    box(45);

    translate(0, 0, -50);
    box(30);
  popMatrix();
}

void setup () {
  size(canvas_width, canvas_height, P3D);
  cam.gotoDefault();
}

void mouseDragged() {
  if (mouseButton == LEFT) {
    cam.translate(pmouseX - mouseX, mouseY - pmouseY);
  }
  else if (mouseButton == CENTER) {
    cam.zoom(pmouseY - mouseY);
  }
  else if (mouseButton == RIGHT) {
    cam.tilt(pmouseX - mouseX);
  }
}
