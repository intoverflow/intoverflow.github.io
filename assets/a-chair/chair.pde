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
  }

  void gotoDefault() {
    m_e1 = new Vec3D(1, 0, 0); /* right ("x") */
    m_e2 = new Vec3D(0, 1, 0); /* zoom ("y") */
    m_e3 = new Vec3D(0, 0, -1); /* up ("z") */
    m_zoom = 400;

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
  fill(127, 127, 127, 127);

  pushMatrix();
    rotateZ(PI/3);

    translate(30, 0, 0);
    rotateX(-PI/6);
    rotateY(PI/3 + 210/float(height) * PI);
    translate(0, 0, -50);
    box(30);

    translate(0, 0, 50);
    box(45);

  popMatrix();

  // println(frameRate);
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
    cam.zoom(pmouseY - mouseY);
  }
  else if (mouseButton == RIGHT) {
    cam.tilt(pmouseX - mouseX);
  }
}
